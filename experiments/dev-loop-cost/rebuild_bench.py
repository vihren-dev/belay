"""Time incremental local Lake builds of one target after a one-line edit of a module.

The question is how long the edit-build loop of model development takes with a local
Lake build, compared with the Nix build, which recompiles a whole package after any
change. For each module, the script appends a new definition (so that the module's
.olean changes and its dependents rebuild), builds, restores the file and builds
again. It prints the seconds and the number of jobs that Lake ran.

Usage: python3 -I rebuild_bench.py PACKAGE_DIR TARGET LAKE MODULE_FILE...
"""

from __future__ import annotations

import re
import subprocess
import sys
import time
from pathlib import Path

PROBE = "\n/-- A temporary definition that a rebuild benchmark appends. -/\ndef rebuildBenchProbe : Nat := 1\n"


def timed_build(package: Path, target: str, lake: str) -> tuple[float, int, str]:
    """Build the target and return seconds, compiled jobs and the last output line."""
    started = time.monotonic()
    result = subprocess.run([lake, "build", target], cwd=package, capture_output=True, text=True, timeout=1800)
    seconds = time.monotonic() - started
    built = len(re.findall(r"Built ", result.stdout))
    last = (result.stdout.strip().splitlines() or ["(no output)"])[-1]
    if result.returncode != 0:
        last = "FAILED: " + (result.stdout + result.stderr)[-400:]
    return seconds, built, last


def main(arguments: list[str]) -> None:
    """Run the no-op build and the edit and restore builds of each module."""
    package, target, lake, files = Path(arguments[0]), arguments[1], arguments[2], [Path(a) for a in arguments[3:]]
    seconds, built, _ = timed_build(package, target, lake)
    print(f"no-op: {seconds:.1f} s, {built} built jobs", flush=True)
    for path in files:
        original = path.read_text()
        try:
            path.write_text(original + PROBE)
            seconds, built, last = timed_build(package, target, lake)
            print(f"edit {path.name}: {seconds:.1f} s, {built} built jobs  [{last[:120]}]", flush=True)
        finally:
            path.write_text(original)
        seconds, built, _ = timed_build(package, target, lake)
        print(f"restore {path.name}: {seconds:.1f} s, {built} built jobs", flush=True)


if __name__ == "__main__":
    main(sys.argv[1:])
