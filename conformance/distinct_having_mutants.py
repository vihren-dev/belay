"""Mutants of DISTINCT, HAVING and aggregates inside expressions (ADR 0018, slice 3).

The task of slice 3 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_distinct_having`.
"""

from conformance.resolve_mutants import SQLITE

RESULTS = SQLITE + "QueryResults.lean"
"""The records of a query, with its groups, HAVING and DISTINCT."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "having_keeps_null": (RESULTS,
        "      if query.having.all fun condition => truthy (condition.eval inGroup source) then\n",
        "      if query.having.all fun condition => !falsy (condition.eval inGroup source) then\n"),
    "aggregate_first_row": (RESULTS,
        "  { context with aggregates := query.aggregates.map (·.eval context group) }\n",
        "  { context with aggregates := query.aggregates.map (·.eval context (group.take 1)) }\n"),
    "distinct_keeps_nulls": (RESULTS,
        "  found.foldl (fun kept record => if kept.any (sameOutput collations ·.1 record.1) then kept else kept ++ [record]) []\n",
        "  found.foldl (fun kept record => if !record.1.any (·.isNull) && kept.any (sameOutput collations ·.1 record.1) then\n"
        "    kept else kept ++ [record]) []\n"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 3: `HAVING` that keeps a group for which it is
NULL, an aggregate in an expression computed over the first row of its group only, and
`DISTINCT` that keeps every NULL row."""

TARGETS: dict[str, tuple[str, ...]] = {
    "having_keeps_null": ("group-having-null",),
    "aggregate_first_row": ("group-aggregate-arithmetic",),
    "distinct_keeps_nulls": ("distinct-values",),
}
"""The authored case of `conformance.authored_distinct_having` that each mutant changes."""

GUARDS: dict[str, str] = {
    "having_keeps_null": "rule:records",
    "aggregate_first_row": "rule:Query.groupContext",
    "distinct_keeps_nulls": "rule:distinctRecords",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
