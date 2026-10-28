"""Choose the smallest complete CI check set; unknown changes still run the Nix test targets.

Scopes, from smallest to largest:

- `docs`: Markdown documentation and review records only; link checks without a build.
- `test`: every Nix test target and the host source tests.
- `infrastructure`: `test`, plus the host Nix tests (`just test-nix`), for changes to
  build definitions or shared test infrastructure.
- `full`: `infrastructure`, plus the scheduled suites of the check job and the mutant suites
  (the CI job `mutants`). Pushes to `main`, manual runs and scheduled runs use it, and
  so do changes to the pinned environment, the parser, the workflows and the build entry points.
"""

import json
import os
from pathlib import Path
import re
import subprocess
from collections.abc import Sequence

from tools.review_records import is_record_path

FULL_EVENTS = {"workflow_dispatch", "schedule"}
"""Events that always run every check on both platforms."""

INFRASTRUCTURE_PREFIXES = ("build-support/", "nix/", "parser/", ".github/")
INFRASTRUCTURE_FILES = {"justfile", ".envrc", "flake.nix", "flake.lock", "lean-toolchain",
                        "pytest.ini", "conftest.py",
                        "tools/ci_checks.py", "tools/check_resources.py",
                        "tests/nix_suites.json", "tests/nix_scheduled_suites.json", "tests/nix_mutant_suites.json",
                        "tests/conformance_frontend.json",
                        "tests/test_source_identity.py", "tests/test_nix_test_targets.py",
                        "tests/environment_snapshot_test.py", "tests/test_test_ownership.py"}
"""Build definitions and shared test infrastructure, which `just test-nix` checks."""

FULL_PREFIXES = ("parser/", "nix/", ".github/")
FULL_FILES = {"build-support/default.nix", "build-support/sources.nix", "build-support/lean-toolchain.nix",
              "lean-toolchain", "justfile"}
"""The pinned environment, the parser, the workflows and the build entry points, which every suite
depends on; a change to one runs every check."""


def is_shared_test_helper(path: str) -> bool:
    """A Python file under tests/ that is not a test module, such as a fixture module.

    Many suites import such helpers, so a change to one selects the host Nix tests,
    which check the Nix test targets and source identities.
    """
    name = Path(path).name
    return (path.startswith("tests/") and path.endswith(".py")
            and not name.startswith("test_") and not name.endswith("_test.py"))




def is_documentation(path: str) -> bool:
    """Markdown at the top level or under docs/ or plans/.

    No build reads these files, so a change of only such files needs only the link checks.
    """
    return path.endswith(".md") and ("/" not in path or path.startswith(("docs/", "plans/")))


def scope(paths: Sequence[str], event: str) -> str:
    """Select the scope for the changed paths; the module docstring describes each scope."""
    if event in FULL_EVENTS or not paths:
        return "full"
    if all(is_documentation(path) or is_record_path(path) for path in paths):
        return "docs"
    if event == "push" or any(path in FULL_FILES or path.startswith(FULL_PREFIXES) for path in paths):
        return "full"
    if any(path in INFRASTRUCTURE_FILES or path.startswith(INFRASTRUCTURE_PREFIXES)
           or is_shared_test_helper(path) for path in paths):
        return "infrastructure"
    return "test"


def main() -> None:
    """Read a bounded Git diff without interpolating event data into shell commands."""
    event = os.environ["GITHUB_EVENT_NAME"]
    payload = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    base = payload.get("pull_request", {}).get("base", {}).get("sha") if event == "pull_request" else payload.get("before")
    paths: list[str] = []
    if event not in FULL_EVENTS:
        if not isinstance(base, str) or re.fullmatch(r"[0-9a-f]{40}", base) is None:
            raise ValueError("CI change selection requires a complete base commit hash")
        if base != "0" * 40:
            result = subprocess.run(["git", "diff", "--name-only", "--no-renames", "-z", base, "HEAD"],
                                    check=True, capture_output=True, timeout=30)
            paths = [path.decode("utf-8", "surrogateescape") for path in result.stdout.split(b"\0") if path]
    selected = scope(paths, event)
    with Path(os.environ["GITHUB_OUTPUT"]).open("a") as output:
        output.write(f"scope={selected}\n")
    print(f"CI scope: {selected}; changed paths: {len(paths)}")


if __name__ == "__main__":
    main()
