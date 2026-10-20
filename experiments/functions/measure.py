"""Measure which SQL functions the out-of-scope corpus cases call (input to the functions ADR).

`python3 experiments/functions/measure.py REPORT CORPUS...` reads the verdict report
(`report.json` of `nix-build integrity/judge.nix -A verdict`) and the frozen cases of each
corpus directory, and prints JSON: for each function that the model does not have, how many
out-of-scope cases call it, how many of them the model refuses for a function reason, and
how many use no other feature that a lexical scan sees ("clean"). It also gives the order of
functions that brings in the most clean cases at each step. A clean case is the best
estimate of a case that the functions bring into scope; a later restriction can still stop
it, so the clean counts are upper bounds.

The scan of each case is lexical; `function_scan.py` describes it.
"""

import gzip
import json
import sys
from collections import Counter
from collections.abc import Iterator
from pathlib import Path

from function_scan import case_features

def records(directory: Path) -> Iterator[dict[str, object]]:
    """The case records of a corpus directory, from its gzipped JSON-lines shards."""
    for path in sorted(directory.rglob("*.jsonl.gz")):
        if "fidelity" in path.parts:
            continue
        with gzip.open(path, "rt") as stream:
            for line in stream:
                yield json.loads(line)


def measure(report: dict[str, dict[str, dict[str, list[str | None]]]], directory: Path) -> dict[str, object]:
    """The function counts of the out-of-scope cases of one corpus."""
    verdicts = report[directory.name]["verdicts"]
    uses: Counter[str] = Counter()
    refused: Counter[str] = Counter()
    clean: Counter[str] = Counter()
    other_uses: Counter[str] = Counter()
    combinations: Counter[str] = Counter()
    total = with_function = clean_total = function_reason = 0
    for case in records(directory):
        verdict, _, reason = verdicts.get(str(case["name"]), [None, None, None])
        if verdict != "MODEL_UNSUPPORTED":
            continue
        total += 1
        reason = reason or ""
        by_function = reason.startswith(("only COUNT(*)", "DISTINCT in a function call",
                                         "A function call with ORDER BY, FILTER or OVER"))
        function_reason += by_function
        functions, other = case_features(case)
        with_function += bool(functions)
        for name in functions:
            uses[name] += 1
            refused[name] += by_function
            if not other:
                clean[name] += 1
        for name in other:
            other_uses[name] += 1
        if functions and not other:
            clean_total += 1
            combinations[",".join(sorted(functions))] += 1
    return {"outOfScope": total, "refusedForFunction": function_reason, "callsUnmodeledFunction": with_function,
            "cleanWithFunction": clean_total,
            "functions": {name: {"uses": uses[name], "refusedForFunction": refused[name], "clean": clean[name]}
                          for name, _ in uses.most_common()},
            "otherFeatures": dict(other_uses.most_common()),
            "greedyOrder": greedy(combinations)}


def greedy(combinations: Counter[str]) -> list[tuple[str, int]]:
    """An order of the functions that brings in the most clean cases at each step: each entry
    is the function and the clean cases whose functions are all supported by then."""
    remaining = {frozenset(key.split(",")): count for key, count in combinations.items()}
    lifted: set[str] = set()
    order: list[tuple[str, int]] = []
    names: set[str] = set().union(*remaining) if remaining else set()

    def covered(supported: set[str]) -> int:
        """The clean cases whose functions are all in the supported set."""
        return sum(count for need, count in remaining.items() if need <= supported)

    while names - lifted:
        best = max(sorted(names - lifted), key=lambda name: covered(lifted | {name}))
        lifted.add(best)
        order.append((best, covered(lifted)))
    return order


def main() -> None:
    """Print the counts of each corpus directory on the command line, as JSON."""
    report = json.loads(Path(sys.argv[1]).read_text())
    print(json.dumps({Path(d).name: measure(report, Path(d)) for d in sys.argv[2:]}, indent=1))


if __name__ == "__main__":
    main()
