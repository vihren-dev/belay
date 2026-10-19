"""Measure which schema features the out-of-scope corpus cases use (input to the schema features ADR).

`python3 experiments/schema-features/measure.py REPORT CORPUS...` reads the verdict report
(`report.json` of `nix-build integrity/judge.nix -A verdict`) and the frozen cases of each
corpus directory, and prints JSON: for each schema feature, how many out-of-scope cases use
it, how many of them the model refuses for a schema reason, and how many use no feature
outside the schema features at all ("clean"). A clean case is the best estimate of a case
that lifting schema restrictions brings into scope; a later restriction can still stop it,
so the clean counts are upper bounds.

The scan is lexical. A small tokenizer drops strings, quoted names, blobs and comments, so a
keyword inside a literal does not count. Statements split at semicolons, except inside the
BEGIN ... END body of CREATE TRIGGER.
"""

import gzip
import json
import re
import sys
from collections import Counter
from pathlib import Path

TOKEN = re.compile(r"""
    (?P<space>\s+) | (?P<line>--[^\n]*) | (?P<block>/\*.*?(\*/|\Z)) |
    (?P<string>'(?:[^']|'')*'?) | (?P<blob>[xX]'[^']*'?) |
    (?P<quoted>"(?:[^"]|"")*"?|`(?:[^`]|``)*`?|\[[^\]]*\]?) |
    (?P<word>[A-Za-z_][A-Za-z_0-9$]*) | (?P<number>\d+(?:\.\d*)?(?:[eE][-+]?\d+)?) |
    (?P<other>.)""", re.VERBOSE | re.DOTALL)


def tokens(sql: str) -> list[str]:
    """The tokens of SQL text: words upper-cased, strings as `'`, quoted names as `"`."""
    result = []
    for match in TOKEN.finditer(sql):
        kind = match.lastgroup
        if kind in ("space", "line", "block"):
            continue
        text = match.group()
        result.append(text.upper() if kind == "word" else "'" if kind in ("string", "blob")
                      else '"' if kind == "quoted" else text)
    return result


def statements(sql: str) -> list[list[str]]:
    """The statements of SQL text as token lists. A trigger body keeps its semicolons."""
    result, current, depth = [], [], 0
    for token in tokens(sql):
        current.append(token)
        if current[:1] == ["CREATE"] and "TRIGGER" in current[:4]:
            if token in ("BEGIN", "CASE"):
                depth += 1
            elif token == "END":
                depth -= 1
        if token == ";" and depth <= 0:
            if current[:-1]:
                result.append(current[:-1])
            current, depth = [], 0
    if current:
        result.append(current)
    return result


def body(statement: list[str]) -> tuple[list[str], list[str]]:
    """The tokens inside the outer parentheses of CREATE TABLE and the tokens after them."""
    if "(" not in statement:
        return [], []
    start, depth = statement.index("("), 0
    for position in range(start, len(statement)):
        depth += {"(": 1, ")": -1}.get(statement[position], 0)
        if depth == 0:
            return statement[start + 1:position], statement[position + 1:]
    return statement[start + 1:], []


def follows(words: list[str], first: str, second: str) -> bool:
    """Whether `second` comes right after `first` somewhere in the tokens."""
    return any(a == first and b == second for a, b in zip(words, words[1:]))


def table_features(statement: list[str]) -> set[str]:
    """The schema features of one CREATE TABLE statement."""
    inside, after = body(statement)
    found = set()
    head = statement[:statement.index("(")] if "(" in statement else statement
    if "AS" in head:
        return {"create-table-as-select"}
    if follows(inside, "CHECK", "("):
        found.add("check")
    if "COLLATE" in inside:
        found.add("collate")
    if "REFERENCES" in inside or follows(inside, "FOREIGN", "KEY"):
        found.add("foreign-key")
    if follows(inside, "GENERATED", "ALWAYS") or follows(inside, "AS", "("):
        found.add("generated-column")
    if "CONSTRAINT" in inside:
        found.add("named-constraint")
    if "AUTOINCREMENT" in inside:
        found.add("autoincrement")
    if follows(inside, "DEFAULT", "("):
        found.add("default-expression")
    if follows(after, "WITHOUT", "ROWID"):
        found.add("without-rowid")
    if "STRICT" in after:
        found.add("strict")
    return found


def index_features(statement: list[str]) -> set[str]:
    """The schema features of one CREATE INDEX statement."""
    keys, after = body(statement)
    found = set()
    if "WHERE" in after:
        found.add("partial-index")
    terms, depth, term = [], 0, []
    for token in keys:
        depth += {"(": 1, ")": -1}.get(token, 0)
        if token == "," and depth == 0:
            terms.append(term); term = []
        else:
            term.append(token)
    terms.append(term)
    for term in terms:
        while term and term[-1] in ("ASC", "DESC"):
            found.add("index-sort-order"); term = term[:-1]
        if "COLLATE" in term:
            found.add("collate"); term = term[:term.index("COLLATE")]
        if len(term) != 1:
            found.add("expression-index")
    return found


OTHER = {
    "trigger": lambda s: s[:1] == ["CREATE"] and "TRIGGER" in s[:4],
    "view": lambda s: s[:1] == ["CREATE"] and "VIEW" in s[:4],
    "virtual-table": lambda s: s[:2] == ["CREATE", "VIRTUAL"],
    "alter-rename-or-drop": lambda s: s[:2] == ["ALTER", "TABLE"] and ("RENAME" in s or "DROP" in s),
    "drop": lambda s: s[:1] == ["DROP"],
    "pragma": lambda s: s[:1] == ["PRAGMA"],
    "other-command": lambda s: s[:1] and s[0] in ("ATTACH", "DETACH", "VACUUM", "REINDEX", "ANALYZE",
                                                   "SAVEPOINT", "RELEASE", "EXPLAIN"),
    "with": lambda s: s[:1] == ["WITH"],
    "subquery": lambda s: follows(s, "(", "SELECT"),
    "compound-select": lambda s: any(t in s for t in ("UNION", "INTERSECT", "EXCEPT")),
    "window": lambda s: "OVER" in s,
    "insert-select": lambda s: s[:1] in (["INSERT"], ["REPLACE"]) and "SELECT" in s and "VALUES" not in s,
}
"""Lexical marks of features outside the schema features; a case with one is not clean."""

SCHEMA_REASONS = ("Unsupported column constraint", "A table option such as WITHOUT ROWID or STRICT",
                  "Unsupported table constraint", "A partial index WHERE clause", "constraints and defaults in a CREATE TABLE",
                  "a CREATE INDEX that runs", "A sort order in a key", "Unsupported SQL form: expr")
"""Out-of-scope reasons that name a schema feature (the first restriction the model met)."""


RUNNING = {"a CREATE INDEX that runs": "create-index-runs",
           "constraints and defaults in a CREATE TABLE that runs": "create-table-runs-with-constraints"}
"""Restrictions on a CREATE that runs in the script rather than describes the starting schema;
the scan takes them from the model's reason, since the SQL alone does not show them."""


def case_features(case: dict, reason: str = "") -> tuple[set[str], set[str]]:
    """The schema features and the other features of one case, over its setup and migration."""
    schema = {feature for prefix, feature in RUNNING.items() if reason.startswith(prefix)}
    other = set()
    for statement in statements((case.get("setupSql") or "") + ";\n" + (case.get("migrationSql") or "")):
        if statement[:1] == ["CREATE"] and "TABLE" in statement[:4] and "VIRTUAL" not in statement[:2]:
            schema |= table_features(statement)
        elif statement[:1] == ["CREATE"] and "INDEX" in statement[:4]:
            schema |= index_features(statement)
        elif statement[:2] == ["ALTER", "TABLE"] and "ADD" in statement:
            schema |= table_features(["("] + statement[statement.index("ADD") + 1:] + [")"])
        other |= {name for name, test in OTHER.items() if test(statement)}
    return schema, other


def records(directory: Path):
    """The case records of a corpus directory."""
    for path in sorted(directory.rglob("*.jsonl.gz")):
        if "fidelity" in path.parts:
            continue
        with gzip.open(path, "rt") as stream:
            for line in stream:
                yield json.loads(line)


def measure(report: dict, directory: Path) -> dict:
    """The feature counts of the out-of-scope cases of one corpus."""
    verdicts = report[directory.name]["verdicts"]
    uses, schema_reason, clean, alone, other_uses = Counter(), Counter(), Counter(), Counter(), Counter()
    total = clean_total = with_schema = 0
    combinations: Counter = Counter()
    for case in records(directory):
        verdict, _, reason = verdicts.get(case["name"], [None, None, None])
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


def greedy(combinations: Counter) -> list[list]:
    """An order of the schema features that brings in the most clean cases at each step: each
    entry is the feature and the clean cases whose schema features are all lifted by then."""
    remaining = {frozenset(key.split(",")): count for key, count in combinations.items()}
    lifted: set[str] = set()
    order = []
    features = set().union(*remaining) if remaining else set()
    while features - lifted:
        def gain(feature: str) -> int:
            return sum(n for need, n in remaining.items() if need <= lifted | {feature})
        best = max(sorted(features - lifted), key=gain)
        lifted.add(best)
        order.append([best, sum(n for need, n in remaining.items() if need <= lifted)])
    return order


def main() -> None:
    report = json.loads(Path(sys.argv[1]).read_text())
    print(json.dumps({Path(d).name: measure(report, Path(d)) for d in sys.argv[2:]}, indent=1))


if __name__ == "__main__":
    main()
