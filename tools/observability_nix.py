"""Run the existing Nix command, recover report artifacts and upload outside the builder."""

import argparse
from pathlib import Path
import sys

from tests.runtime_support import CommandTimeout, run_command
from tools.observability_logs import recover
from tools.observability_records import diagnostic
from tools.observability_spool import attempt_upload, import_execution, spool


def collect_outputs(output: str, destination: Path) -> None:
    """Read each successful output or link-farm child without copying runtime store closures."""
    for line in output.splitlines():
        root = Path(line.strip())
        if not line.startswith("/nix/store/") or not root.is_dir():
            continue
        folders = [root, *(child for child in root.iterdir() if child.is_dir())]
        for folder in folders:
            for manifest in (folder / "observability").glob("*/execution.json"):
                import_execution(manifest.parent, destination)


def run(arguments: list[str], timeout: int) -> int:
    """Keep the build status even when log extraction or delivery fails."""
    attempt_upload()
    try:
        result = run_command(arguments, cwd=Path.cwd(), timeout=timeout, echo=True)
    except CommandTimeout as error:
        result = error.result
    try:
        collect_outputs(result.stdout, spool())
        recover((result.stdout + "\n" + result.stderr).splitlines(), spool())
    except (OSError, ValueError, KeyError) as error:
        diagnostic(f"artifact recovery failed ({type(error).__name__}); inspect the retained build log")
    attempt_upload()
    return 124 if result.timed_out else result.returncode


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=int, required=True)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    sys.exit(run(args.command, args.timeout))
