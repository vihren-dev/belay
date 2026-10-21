"""Check that two conformance runtimes give the same predictions, and time them.

A local Lake build of the runner is useful in the edit loop only if it predicts what
the Nix-built runner predicts. This script runs `python -m conformance.predict` with
each runtime root over every judge input file and reports differing files and the
seconds that each runtime took.

Usage: python3 -I compare_predictions.py REPOSITORY INPUT_DIR RUNTIME_A RUNTIME_B
"""

from __future__ import annotations

import os
import subprocess
import sys
import time
from pathlib import Path


def predict(repository: Path, runtime: Path, given: Path) -> tuple[str, float]:
    """Return the predictions for one input file and the seconds they took."""
    started = time.monotonic()
    result = subprocess.run([sys.executable, "-m", "conformance.predict", "--runtime", str(runtime)],
                            stdin=given.open(), capture_output=True, text=True, timeout=900, cwd=repository,
                            env={**os.environ, "PYTHONPATH": str(repository)}, check=True)
    return result.stdout, time.monotonic() - started


def main(arguments: list[str]) -> None:
    """Compare the two runtimes on each input file."""
    repository, inputs, first, second = (Path(a).resolve() for a in arguments)
    totals, different = [0.0, 0.0], []
    for given in sorted(inputs.glob("*.jsonl")):
        output_a, seconds_a = predict(repository, first, given)
        output_b, seconds_b = predict(repository, second, given)
        totals[0] += seconds_a
        totals[1] += seconds_b
        if output_a != output_b:
            different.append(given.name)
    print(f"files {len(list(inputs.glob('*.jsonl')))}, different {len(different)} {different[:5]}")
    print(f"seconds: {first.name} {totals[0]:.1f}, {second.name} {totals[1]:.1f}")


if __name__ == "__main__":
    main(sys.argv[1:])
