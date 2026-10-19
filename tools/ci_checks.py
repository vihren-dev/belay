"""Run complete native gates with Darwin's bundle before concurrent suite builds."""

import argparse
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
from time import monotonic

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tools.check_resources import check_resources
from tests.runtime_support import CommandTimeout, run_command

SCOPE_RECIPES = {
    "test": ["test-full"],
    "infrastructure": ["test-full", "test-nix"],
    "packaging": ["test-full", "runtime-package"],
    "package": ["package"],
}
"""The `just` recipes for each scope of tests/ci_scope.py; one invocation runs shared dependencies once."""

BUNDLE_FIRST_SYSTEM = "aarch64-darwin"
"""Darwin completes the bundle gate before the complete recipe starts other test builders."""
BUNDLE_BUILD_LIMIT_SECONDS = 1500
"""The limit of the justfile recipes that build test suites: more than the per-suite limit in
build-support/tests.nix, so a bundle suite that hangs fails with its own name."""
NIX_TEST_BUILD_OPTIONS = ("--option", "sandbox", "true", "--option", "sandbox-fallback", "false",
                          "--extra-experimental-features", "nix-command flakes")
"""Use the complete test recipes' sandbox policy for the isolated bundle target."""


def run_checks(scope: str, mode: str, system: str, root: Path) -> None:
    """Use all complete gates and isolate Darwin's bundle phase from model and upstream builders."""
    if scope not in SCOPE_RECIPES or mode not in {"source", "build"}:
        raise ValueError(f"Unknown CI scope or build mode: {scope}, {mode}; use a scope from tests/ci_scope.py")
    check_resources(root)
    if os.environ.get("SQLITE_VERIFIER_SYSTEM") != system:
        raise ValueError("Pinned shell system differs from the selected native CI system")
    environment = dict(os.environ)
    for variable in ("SQLITE_VERIFIER_RUNTIME_ROOT", "SQLITE_VERIFIER_UNIT_CHECKS"):
        environment.pop(variable, None)
    records: list[dict[str, object]] = []
    output = root / "build/ci-phases.json"
    output.parent.mkdir(exist_ok=True)

    def run(name: str, command: list[str], timeout: int) -> str:
        """Run one phase with its output streamed to the log; keep its duration and status."""
        started = monotonic()
        status = -1
        artifacts = root / "build/ci-phases" / name
        try:
            result = run_command(command, cwd=root, environment=environment, timeout=timeout,
                                 artifacts=artifacts, echo=True)
            status = result.returncode
            if status:
                raise subprocess.CalledProcessError(status, command, result.stdout, result.stderr)
            return result.stdout.strip()
        except CommandTimeout as error:
            status = error.result.returncode
            print(f"Phase {name} stopped after its {timeout}-second limit: {shlex.join(command)}. "
                  f"Its output is in the log above and in {artifacts.relative_to(root)}/.",
                  file=sys.stderr, flush=True)
            raise
        finally:
            records.append({"phase": name, "command": command, "exit_code": status,
                            "elapsed_seconds": monotonic() - started})
            output.write_text(json.dumps(records, indent=2) + "\n")

    if mode == "build":
        environment["SQLITE_VERIFIER_RUNTIME_ROOT"] = run("runtime",
            ["nix-build", "build-support/default.nix", "-A", "runtime", "--no-out-link",
             "--extra-experimental-features", "nix-command flakes"], 900)
        runtime = Path(environment["SQLITE_VERIFIER_RUNTIME_ROOT"])
    elif mode == "source":
        run("setup", ["just", "setup"], 330)
    else:
        raise ValueError(f"Unknown build mode: {mode}")
    toolchain = (runtime if mode == "build" else root) / "lean/bin"
    lean = str(toolchain / "lean") if toolchain.is_dir() else "lean"
    lake = str(toolchain / "lake") if toolchain.is_dir() else "lake"
    versions = {"python": sys.version,
                "lean": run("lean-version", [lean, "--version"], 10),
                "lake": run("lake-version", [lake, "--version"], 10)}
    (root / "build/ci-environment.json").write_text(json.dumps(versions, indent=2) + "\n")
    if system == BUNDLE_FIRST_SYSTEM:
        run("bundle", ["nix-build", "build-support/default.nix", "-A", "tests.bundle",
            "--out-link", "build/nix-tests-bundle", *NIX_TEST_BUILD_OPTIONS], BUNDLE_BUILD_LIMIT_SECONDS)
    run("checks-" + scope, ["just", *SCOPE_RECIPES[scope]], 1800)


def main() -> None:
    """Accept only the scopes of tests/ci_scope.py and the two native supported platforms."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scope", choices=tuple(SCOPE_RECIPES), required=True)
    parser.add_argument("--mode", choices=("source", "build"), default="source")
    parser.add_argument("--system", choices=("x86_64-linux", "aarch64-darwin"), required=True)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    arguments = parser.parse_args()
    try:
        run_checks(arguments.scope, arguments.mode, arguments.system, arguments.root.resolve())
    except CommandTimeout:
        # The phase output is already in the log; the exception text would repeat all of it.
        sys.exit(1)


if __name__ == "__main__":
    main()
