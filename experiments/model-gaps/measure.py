"""Which model work of ADR 0017's D5 brings which out-of-scope corpus cases into scope.

`python3 experiments/model-gaps/measure.py VERDICT/report.json CORPUS_DIR...` reads the cases with
the verdict `MODEL_UNSUPPORTED`, marks their features with the lexical scan of the functions
measurement (`experiments/functions/function_scan.py`, with the function list of the model after
ADR 0015), and prints JSON per corpus: for each group of model work, the cases that use it and
the cases that it alone would make clean, the cases that all groups together make clean, and a
greedy order of the groups.
"""

import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "functions"))
import function_scan  # noqa: E402
from function_scan import case_features  # noqa: E402
from measure import records  # noqa: E402
from scan import statements  # noqa: E402

function_scan.MODELED = {name.upper() for name in (
    "abs avg ceil ceiling char coalesce concat concat_ws count date datetime degrees floor format glob "
    "group_concat hex if ifnull iif instr json json_array json_array_length jsonb jsonb_array jsonb_extract "
    "jsonb_group_array jsonb_group_object jsonb_insert jsonb_object jsonb_patch jsonb_remove jsonb_replace "
    "jsonb_set json_error_position json_extract json_group_array json_group_object json_insert json_object "
    "json_patch json_pretty json_quote json_remove json_replace json_set json_type json_valid julianday "
    "length like likelihood likely lower ltrim max min mod nullif octet_length pi printf quote radians "
    "replace round rtrim sign sqrt strftime string_agg substr substring sum time total trim trunc typeof "
    "unhex unicode unistr unistr_quote unixepoch unlikely upper zeroblob json_each").split()} | {"MIN2", "MAX2"}
"""The functions that the model resolves after ADR 0015, from `Resolution/FunctionCalls.lean`,
`Resolution/Calls.lean` and `Resolution/ExprForms.lean`."""

GROUPS = {
    "subqueries": {"subquery"},
    "in-list": {"in-list"},
    "between": {"between"},
    "case": {"case"},
    "concat": {"concat-operator"},
    "distinct-having": {"distinct-or-having"},
    "foreign-keys": {"foreign-keys"},
    "triggers": {"trigger"},
}
"""The groups of model work in D5 of ADR 0017, by the marks of the scan that each removes.
`foreign-keys` is `PRAGMA foreign_keys`, which turns enforcement on; the scan's own `pragma`
mark then counts only the other pragmas."""


def features(case: dict[str, object]) -> set[str]:
    """Every mark of one case: its unmodeled functions, its other features, and
    `foreign-keys` in place of `pragma` for a `PRAGMA foreign_keys` statement."""
    functions, other = case_features(case)
    pragmas = [s for s in statements(str(case.get("migrationSql") or "")) + statements(str(case.get("setupSql") or ""))
               if s[:1] == ["PRAGMA"]]
    if pragmas and all(s[1:2] == ["FOREIGN_KEYS"] for s in pragmas):
        other = (other - {"pragma"}) | {"foreign-keys"}
    elif any(s[1:2] == ["FOREIGN_KEYS"] for s in pragmas):
        other |= {"foreign-keys"}
    return {"call:" + name for name in functions} | other


def measure(report: dict[str, object], directory: Path) -> dict[str, object]:
    """The counts of one corpus."""
    verdicts = report[directory.name]["verdicts"]
    marked = [features(case) for case in records(directory) if verdicts.get(case["name"], [""])[0] == "MODEL_UNSUPPORTED"]
    every = set().union(*GROUPS.values())
    result: dict[str, object] = {"outOfScope": len(marked), "withAnyMark": sum(1 for marks in marked if marks),
                                 "unmarked": sum(1 for marks in marked if not marks)}
    result["groups"] = {name: {"uses": sum(1 for marks in marked if marks & group),
                               "aloneClean": sum(1 for marks in marked if marks and marks <= group)}
                        for name, group in GROUPS.items()}
    result["allGroupsClean"] = sum(1 for marks in marked if marks and marks <= every)
    chosen: set[str] = set()
    order = []
    remaining = dict(GROUPS)
    while remaining:
        best = max(remaining, key=lambda name: sum(1 for marks in marked if marks and marks <= chosen | remaining[name]))
        chosen |= remaining.pop(best)
        order.append([best, sum(1 for marks in marked if marks and marks <= chosen)])
    result["greedyOrder"] = order
    result["otherMarksOfAlmostClean"] = Counter(mark for marks in marked if len(marks - every) == 1
                                                 for mark in marks - every).most_common(15)
    return result


if __name__ == "__main__":
    loaded = json.loads(Path(sys.argv[1]).read_text())
    print(json.dumps({Path(path).name: measure(loaded, Path(path)) for path in sys.argv[2:]}, indent=1))
