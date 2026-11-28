"""Measure the kernel cost of two representations of a bag of model rows.

The ADR for query results as bags must choose how the model stores a bag of rows: as a
quotient of lists by permutation, or as the sorted list that the model uses now
(`Resolved.normalForm`). Model tests decide outputs with `decide +kernel`, so this script
measures how long the kernel takes to decide that two orders of the same rows give equal bags,
for each representation and for several row counts. It writes one Lean file for each case,
compiles it with the pinned toolchain and model package, and records the time of the best of
three runs minus the time of a file that has only the imports. All runs have fixed deadlines.
"""

import json
from pathlib import Path
import subprocess
import sys
import time

HEADER = """import Belay.Sqlite.Model.Shared.Execution.PossibleResults
open Belay.Sqlite.Model

/-- A row of two integer values; the first value repeats, so the rows have ties. -/
def row (i : Nat) : List Value := [.integer (Int.ofNat (i * 7 % 13)), .integer (Int.ofNat i)]
/-- A bag of rows as a quotient of lists by permutation. -/
abbrev Bag := Quotient (List.isSetoid (List Value))
instance : DecidableEq Bag := fun a b =>
  @Quotient.decidableEq _ _ (fun l₁ l₂ => List.decidablePerm l₁ l₂) a b
/-- The bag of the rows of a list. -/
def bagOf (l : List (List Value)) : Bag := Quotient.mk _ l
"""

CASES = {
    "quotient": "example : bagOf ((List.range {n}).map row) = "
                "bagOf ((List.range {n}).reverse.map row) := by decide +kernel\n",
    "normal-form": "example : Resolved.normalForm ((List.range {n}).map row) = "
                   "Resolved.normalForm ((List.range {n}).reverse.map row) := by decide +kernel\n",
}
SIZES = [10, 50, 100, 200]
RUNS = 3


def compile_seconds(path: Path) -> float:
    """Compile one file and return the best wall time of three runs; fail on any diagnostic."""
    best = None
    for _ in range(RUNS):
        start = time.monotonic()
        result = subprocess.run(["lean", str(path)], capture_output=True, text=True,
                                timeout=600, check=False)
        elapsed = time.monotonic() - start
        if result.returncode or result.stdout or result.stderr:
            raise RuntimeError(f"{path.name} failed:\n{result.stdout}{result.stderr}")
        best = elapsed if best is None else min(best, elapsed)
    return best


def main(output: Path) -> None:
    """Write, compile and time every case, and record the results as JSON."""
    work = Path("kernel-cost")
    work.mkdir(exist_ok=True)
    baseline_file = work / "Baseline.lean"
    baseline_file.write_text(HEADER)
    baseline = compile_seconds(baseline_file)
    results = {"baseline_seconds": round(baseline, 3), "runs": RUNS, "cases": []}
    for name, template in CASES.items():
        for n in SIZES:
            path = work / f"Cost_{name.replace('-', '_')}_{n}.lean"
            path.write_text(HEADER + "\n" + template.format(n=n))
            seconds = compile_seconds(path) - baseline
            results["cases"].append({"representation": name, "rows": n,
                                     "kernel_seconds": round(max(seconds, 0.0), 3)})
            print(f"{name} {n}: {seconds:.3f} s", flush=True)
    (output / "kernel-cost.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main(Path(sys.argv[1]))
