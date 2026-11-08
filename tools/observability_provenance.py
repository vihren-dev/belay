"""The provenance of the test executions that a host command runs (#332).

A pytest session outside a Nix builder writes these values into its own `metadata`, and the
host Nix wrapper adds them to each execution whose builder ran during the command, so a query
can separate CI from local runs, platforms, commits and suites.
The values come from an allowlist of GitHub Actions variables and, locally, from jj. They are
never derivation inputs: builders write `metadata: {}`, and the host adds the values on import.
"""

from collections.abc import Callable, Mapping
from pathlib import Path
import platform
import subprocess

ROOT = Path(__file__).resolve().parents[1]
"""The checkout whose working copy a local command tests."""
CI_FIELDS = {"event": "GITHUB_EVENT_NAME", "commit": "GITHUB_SHA", "run_id": "GITHUB_RUN_ID",
             "run_attempt": "GITHUB_RUN_ATTEMPT", "job": "GITHUB_JOB"}
"""The metadata fields and the GitHub Actions variables that they copy; no other variable is read."""
JJ_SECONDS = 5
"""A slow or locked jj leaves the local commit absent instead of delaying the test command."""


def nix_system(machine: str, system: str) -> str:
    """The Nix system name of a host, such as `x86_64-linux` or `aarch64-darwin`, which the CI
    matrix and the Nix outputs use; Python reports Apple silicon as `arm64` and macOS as `Darwin`."""
    return f"{'aarch64' if machine == 'arm64' else machine}-{system.lower()}"


def working_copy() -> dict[str, str]:
    """The jj commit and change IDs of the last snapshot of the working copy `@`, or nothing.

    `--ignore-working-copy` keeps the test command from snapshotting or changing the working
    copy, so edits after the last jj command are not in this commit."""
    try:
        result = subprocess.run(["jj", "--ignore-working-copy", "log", "--no-graph", "-r", "@", "-T",
                                 'commit_id ++ " " ++ change_id'], cwd=ROOT, capture_output=True,
                                text=True, timeout=JJ_SECONDS, check=False)
    except (OSError, subprocess.SubprocessError):
        return {}
    parts = result.stdout.split()
    return {"commit": parts[0], "change": parts[1]} if result.returncode == 0 and len(parts) == 2 else {}


def provenance(environment: Mapping[str, str], local_commit: Callable[[], dict[str, str]] = working_copy,
               host: tuple[str, str] | None = None) -> dict[str, str]:
    """The metadata of an execution that this command runs: the event, the platform and, on
    GitHub Actions, the run, attempt, job and commit; locally the jj commit and change.
    A value that is not available is absent."""
    machine, system = host or (platform.machine(), platform.system())
    values = {"platform": nix_system(machine, system)}
    if environment.get("GITHUB_ACTIONS") == "true":
        values.update({field: environment[name] for field, name in CI_FIELDS.items() if environment.get(name)})
    else:
        values.update({"event": "local", **local_commit()})
    return values
