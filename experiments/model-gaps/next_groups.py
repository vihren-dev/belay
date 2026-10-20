"""Which model work after ADR 0018 brings which out-of-scope corpus cases into scope.

`python3 experiments/model-gaps/next_groups.py VERDICT/report.json CORPUS_DIR...` marks the cases
with the verdict `MODEL_UNSUPPORTED` as `measure.py` does, counts every group of ADR 0018 as
done, and prints JSON per corpus: for each candidate group, the cases that use it and the cases
that it and ADR 0018 together make clean; a greedy order of the candidates; and the pragmas that
the cases run. Three marks of the scan are corrected: `IS` and `LIKE` are modeled, and the
bitwise operators are counted without `%`, which the model has.
"""

import importlib.util
import json
import sys
from collections import Counter
from pathlib import Path

_spec = importlib.util.spec_from_file_location("gaps", Path(__file__).with_name("measure.py"))
assert _spec and _spec.loader
gaps = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gaps)

DONE = set().union(*gaps.GROUPS.values())
"""The marks that the groups of ADR 0018 remove."""
CANDIDATES = {
    "pragmas": {"pragma"},
    "compound-select": {"compound-select"},
    "insert-select": {"insert-select"},
    "alter-rename-drop": {"alter-rename-or-drop"},
    "views": {"view"},
    "with": {"with"},
    "parameters": {"parameter"},
    "bitwise": {"bitwise"},
}
"""The candidate groups of the next model ADR, by the marks that each removes."""


def bitwise(statement: list[str]) -> bool:
    """Whether a statement has a bitwise operator: `&`, `~`, `<<`, `>>` or a single `|`."""
    return (any(token in ("&", "~") for token in statement) or gaps.function_scan.follows(statement, "<", "<")
            or gaps.function_scan.follows(statement, ">", ">") or gaps.function_scan.single_bar(statement))


def marks(case: dict[str, object]) -> set[str]:
    """The marks of `measure.features` with the corrections of the module documentation."""
    found = gaps.features(case) - {"is-operator", "like-glob", "bitwise-or-modulo"}
    text = str(case.get("migrationSql") or "") + "\n" + str(case.get("setupSql") or "")
    return found | ({"bitwise"} if any(bitwise(statement) for statement in gaps.statements(text)) else set())


def measure(report: dict[str, object], directory: Path) -> dict[str, object]:
    """The counts of one corpus."""
    verdicts = report[directory.name]["verdicts"]
    cases = [case for case in gaps.records(directory) if verdicts.get(case["name"], [""])[0] == "MODEL_UNSUPPORTED"]
    marked = [marks(case) for case in cases]

    def clean(groups: set[str]) -> int:
        """The cases whose marks the groups of ADR 0018 and these groups all remove."""
        return sum(1 for found in marked if found and found <= DONE | groups)

    result: dict[str, object] = {"outOfScope": len(marked), "cleanAfterAdr0018": clean(set()),
                                 "groups": {name: {"uses": sum(1 for found in marked if found & group),
                                                   "cleanWithAdr0018": clean(group)}
                                            for name, group in CANDIDATES.items()}}
    chosen: set[str] = set()
    order, remaining = [], dict(CANDIDATES)
    while remaining:
        best = max(remaining, key=lambda name: clean(chosen | remaining[name]))
        chosen |= remaining.pop(best)
        order.append([best, clean(chosen)])
    result["greedyOrder"] = order
    pragmas = Counter(statement[1] for case in cases
                      for statement in gaps.statements(str(case.get("migrationSql") or "") + "\n" +
                                                       str(case.get("setupSql") or ""))
                      if statement[:1] == ["PRAGMA"] and len(statement) > 1)
    result["pragmaStatements"] = pragmas.most_common(10)
    result["casesWithPragma"] = Counter(name for case in cases for name in {
        statement[1] for statement in gaps.statements(str(case.get("migrationSql") or "") + "\n" +
                                                      str(case.get("setupSql") or ""))
        if statement[:1] == ["PRAGMA"] and len(statement) > 1}).most_common(10)
    return result


if __name__ == "__main__":
    loaded = json.loads(Path(sys.argv[1]).read_text())
    print(json.dumps({Path(path).name: measure(loaded, Path(path)) for path in sys.argv[2:]}, indent=1))
