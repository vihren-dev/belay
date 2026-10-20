"""Measure which SQL functions the out-of-scope corpus cases call (input to the functions ADR).

`python3 experiments/functions/measure.py REPORT CORPUS...` reads the verdict report
(`report.json` of `nix-build integrity/judge.nix -A verdict`) and the frozen cases of each
corpus directory, and prints JSON: for each function that the model does not have, how many
out-of-scope cases call it, how many of them the model refuses for a function reason, and
how many use no other feature that a lexical scan sees ("clean"). It also gives the order of
functions that brings in the most clean cases at each step. A clean case is the best
estimate of a case that the functions bring into scope; a later restriction can still stop
it, so the clean counts are upper bounds.

The scan reuses the tokenizer and the marks of other features of
`experiments/schema-features/scan.py`, and adds the expression and query forms that the
model refuses today.
"""

import gzip
import json
import sys
from collections import Counter
from collections.abc import Iterator
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "schema-features"))
from scan import OTHER, follows, statements  # noqa: E402

MODELED = {"COUNT", "MIN", "MAX", "SUM", "AVG", "COALESCE", "JSON_EXTRACT", "JSON_TYPE", "JSON_VALID",
           "JSON_ARRAY_LENGTH", "JSON", "DATE", "TIME", "DATETIME", "JULIANDAY", "UNIXEPOCH", "STRFTIME",
           "JSON_EACH"}
"""The functions that the model has today. MIN and MAX with two or more arguments are the
scalar functions, which the model does not have; the scan counts them as `MIN2` and `MAX2`."""

NOT_CALLS = {"IN", "EXISTS", "VALUES", "KEY", "CHECK", "UNIQUE", "AS", "ON", "USING", "OVER", "FILTER",
             "AND", "OR", "NOT", "WHERE", "SELECT", "FROM", "JOIN", "SET", "INTO", "TABLE", "INDEX",
             "REFERENCES", "WITH", "RECURSIVE", "VIEW", "TRIGGER", "WHEN", "THEN", "ELSE", "CASE",
             "BETWEEN", "LIKE", "GLOB", "IS", "BY", "DEFAULT", "COLLATE", "RETURNING", "LIMIT", "OFFSET",
             "HAVING", "GROUP", "ORDER", "UPDATE", "DELETE", "INSERT", "REPLACE_INTO", "CAST", "RAISE",
             "PRIMARY", "FOREIGN", "CONSTRAINT", "GENERATED", "ALWAYS", "STORED", "VIRTUAL", "EXCEPT",
             "UNION", "INTERSECT", "ALL", "DISTINCT", "IF", "CONFLICT", "DO", "NOTHING", "ROWID"}
"""Words before `(` that are no function call: keywords, and CAST, which is an expression form."""

BEFORE_CALL = {"SELECT", "WHERE", "AND", "OR", "NOT", "BY", "THEN", "ELSE", "WHEN", "CASE", "RETURNING",
               "HAVING", "DISTINCT", "ALL", "LIMIT", "OFFSET", "IS", "LIKE", "GLOB", "BETWEEN", "ESCAPE", "DEFAULT",
               "AS", "VALUES", "SET", "ON", "FROM", "JOIN", "COLLATE"}
"""Words after which `name (` is a call; after any other word it is a type name, such as
`VARCHAR(10)`, or a table name with a column list."""

AFTER_NAME = {"INTO", "TABLE", "ON", "REFERENCES", "INDEX", "EXISTS", "VIEW", "TRIGGER", ".", "UPDATE", "KEY"}
"""Tokens after which `name (` is a table or column list, not a call."""

def single_bar(statement: list[str]) -> bool:
    """Whether the statement has a `|` that is not part of `||`: the bitwise OR operator."""
    bars = [position for position, token in enumerate(statement) if token == "|"]
    return any(position - 1 not in bars and position + 1 not in bars for position in bars)


FORMS = {
    "between": lambda s: "BETWEEN" in s,
    "case": lambda s: "CASE" in s,
    "concat-operator": lambda s: follows(s, "|", "|"),
    "in-list": lambda s: follows(s, "IN", "("),
    "like-glob": lambda s: any(t in s for t in ("LIKE", "GLOB", "REGEXP", "MATCH")),
    "is-operator": lambda s: any(t == "IS" and s[i + 1:i + 2] != ["NULL"] and s[i + 1:i + 3] != ["NOT", "NULL"]
                                 for i, t in enumerate(s)),
    "bitwise-or-modulo": lambda s: any(t in ("&", "~", "%") for t in s) or follows(s, "<", "<")
                                   or follows(s, ">", ">") or single_bar(s),
    "parameter": lambda s: any(t in ("?", ":", "@", "$") for t in s),
    "distinct-or-having": lambda s: "DISTINCT" in s or "HAVING" in s,
    "explain": lambda s: s[:1] == ["EXPLAIN"],
}
"""Lexical marks of expression and query forms that the model refuses today."""


def records(directory: Path) -> Iterator[dict[str, object]]:
    """The case records of a corpus directory, from its gzipped JSON-lines shards."""
    for path in sorted(directory.rglob("*.jsonl.gz")):
        if "fidelity" in path.parts:
            continue
        with gzip.open(path, "rt") as stream:
            for line in stream:
                yield json.loads(line)


def calls(statement: list[str]) -> tuple[set[str], set[str]]:
    """The function names that the statement calls, and the call forms that the model refuses:
    `distinct-call` (`f(DISTINCT ...)`), `filter-or-over` and `table-function` (a call in FROM
    or JOIN other than `json_each`)."""
    names: set[str] = set()
    forms: set[str] = set()
    for position, token in enumerate(statement[:-1]):
        if statement[position + 1] != "(" or not token[:1].isalpha() or token in NOT_CALLS:
            continue
        before = statement[position - 1] if position else ""
        if before in AFTER_NAME or (before[:1].isalpha() and before not in BEFORE_CALL):
            continue
        if before in ("FROM", "JOIN", ","):
            if before != "," and token != "JSON_EACH":
                forms.add("table-function")
            if before != ",":
                continue
        arguments, depth, end = 1, 0, position + 1
        for end in range(position + 1, len(statement)):
            depth += {"(": 1, ")": -1}.get(statement[end], 0)
            if depth == 1 and statement[end] == ",":
                arguments += 1
            if depth == 0:
                break
        if end + 1 < len(statement) and statement[end + 1] == "AS" and before in (",", "WITH", "RECURSIVE"):
            continue
        if statement[position + 2:position + 3] == ["DISTINCT"]:
            forms.add("distinct-call")
        if end + 1 < len(statement) and statement[end + 1] in ("FILTER", "OVER"):
            forms.add("filter-or-over")
        names.add(token + "2" if token in ("MIN", "MAX") and arguments >= 2 else token)
    return names - MODELED, forms


def case_features(case: dict[str, object]) -> tuple[set[str], set[str]]:
    """The unmodeled functions and the other features of one case. The migration counts, and
    the CREATE statements of the setup, whose index keys, CHECK constraints and generated
    columns the model resolves."""
    functions: set[str] = set()
    other: set[str] = set()
    migration = statements(str(case.get("migrationSql") or ""))
    setup = [s for s in statements(str(case.get("setupSql") or "")) if s[:1] == ["CREATE"]]
    for statement in migration + setup:
        names, forms = calls(statement) if statement[:1] != ["PRAGMA"] else (set(), set())
        functions |= names
        other |= forms
        other |= {name for name, test in OTHER.items() if test(statement)}
        if statement in migration:
            other |= {name for name, test in FORMS.items() if test(statement)}
    return functions, other


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
