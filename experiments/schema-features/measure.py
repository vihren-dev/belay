"""Measure which schema features the out-of-scope corpus cases use (input to the schema features ADR).

`python3 experiments/schema-features/measure.py REPORT CORPUS...` reads the verdict report
(`report.json` of `nix-build integrity/judge.nix -A verdict`) and the frozen cases of each
corpus directory, and prints JSON: for each schema feature, how many out-of-scope cases use
it, how many of them the model refuses for a schema reason, and how many use no feature
outside the schema features at all ("clean"). A clean case is the best estimate of a case
that lifting schema restrictions brings into scope; a later restriction can still stop it,
so the clean counts are upper bounds.

The scan of each case is lexical; `scan.py` describes it.
"""

import gzip
import json
import sys
from collections import Counter
from collections.abc import Iterator
from pathlib import Path

from scan import SCHEMA_REASONS, case_features

Report = dict[str, dict[str, dict[str, list[str | None]]]]
"""The verdict report: for each corpus, the verdict, position and reason of each case."""


def records(directory: Path) -> Iterator[dict[str, object]]:
    """The case records of a corpus directory, from its gzipped JSON-lines shards."""
    for path in sorted(directory.rglob("*.jsonl.gz")):
        if "fidelity" in path.parts:
            continue
        with gzip.open(path, "rt") as stream:
            for line in stream:
                yield json.loads(line)


def measure(report: Report, directory: Path) -> dict[str, object]:
    """The feature counts of the out-of-scope cases of one corpus."""
    verdicts = report[directory.name]["verdicts"]
    uses: Counter[str] = Counter()
    schema_reason: Counter[str] = Counter()
    clean: Counter[str] = Counter()
    alone: Counter[str] = Counter()
    other_uses: Counter[str] = Counter()
    total = clean_total = with_schema = 0
    combinations: Counter[str] = Counter()
    for case in records(directory):
        verdict, _, reason = verdicts.get(str(case["name"]), [None, None, None])
        if verdict != "MODEL_UNSUPPORTED":
            continue
        total += 1
        reason = reason or ""
        schema, other = case_features(case, reason)
        with_schema += bool(schema)
        for feature in schema:
            uses[feature] += 1
            if reason.startswith(SCHEMA_REASONS):
                schema_reason[feature] += 1
            if not other:
                clean[feature] += 1
                if len(schema) == 1:
                    alone[feature] += 1
        for feature in other:
            other_uses[feature] += 1
        if schema and not other:
            clean_total += 1
            combinations[",".join(sorted(schema))] += 1
    return {"outOfScope": total, "usesSchemaFeature": with_schema,
            "cleanWithSchemaFeature": clean_total,
            "features": {feature: {"uses": uses[feature], "schemaReason": schema_reason[feature],
                                   "clean": clean[feature], "only": alone[feature]}
                         for feature, _ in uses.most_common()},
            "otherFeatures": dict(other_uses.most_common()),
            "cleanCombinations": dict(combinations.most_common(25)),
            "greedyOrder": greedy(combinations)}


def greedy(combinations: Counter[str]) -> list[tuple[str, int]]:
    """An order of the schema features that brings in the most clean cases at each step: each
    entry is the feature and the clean cases whose schema features are all lifted by then."""
    remaining = {frozenset(key.split(",")): count for key, count in combinations.items()}
    lifted: set[str] = set()
    order: list[tuple[str, int]] = []
    features: set[str] = set().union(*remaining) if remaining else set()

    def covered(supported: set[str]) -> int:
        """The clean cases whose schema features are all in the supported set."""
        return sum(count for need, count in remaining.items() if need <= supported)

    while features - lifted:
        best = max(sorted(features - lifted), key=lambda feature: covered(lifted | {feature}))
        lifted.add(best)
        order.append((best, covered(lifted)))
    return order


def main() -> None:
    """Print the counts of each corpus directory on the command line, as JSON."""
    report: Report = json.loads(Path(sys.argv[1]).read_text())
    print(json.dumps({Path(d).name: measure(report, Path(d)) for d in sys.argv[2:]}, indent=1))


if __name__ == "__main__":
    main()
