"""Mutants of queries without FROM (ADR 0012, amendment 5, slice 6a).

The task of slice 6a lists the changes that the conformance suite must notice. Each
mutant is one text change in a copy of the model, which
`conformance.resolve_mutants.measure` builds and runs against its target case of
`conformance.authored_fromless`. `conformance.query_mutants` already has the mutant that
gives an aggregate over zero rows no row (`empty_aggregate_no_row`).
"""

from conformance.resolve_mutants import SQLITE

FUNCTIONS = SQLITE + "QueryFunctions.lean"
"""The source rows of a query, joined from the one row with no cells."""
QUERIES = SQLITE + "Resolution/Queries.lean"
"""The resolution of a SELECT."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "fromless_no_row": (FUNCTIONS, "{ rows := [[]], width := 0, fault := .none }",
        "{ rows := [], width := 0, fault := .none }"),
    "fromless_two_rows": (FUNCTIONS, "{ rows := [[]], width := 0, fault := .none }",
        "{ rows := [[], []], width := 0, fault := .none }"),
    "fromless_where_ignored": (QUERIES,
        "    return { sources, filter := condition,",
        "    return { sources, filter := if sources.isEmpty then none else condition,"),
    "fromless_star_accepted": (QUERIES, "  | .star => if scope.isEmpty then .error (.prepare .noTablesSpecified) else",
        "  | .star => if false then .error (.prepare .noTablesSpecified) else"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the
replacement. The names follow the list in the task of slice 6a: the source has no row;
the source has two rows; the WHERE of a query without FROM is ignored; `*` without FROM
is accepted."""

TARGETS: dict[str, tuple[str, ...]] = {
    "fromless_no_row": ("fromless-values",), "fromless_two_rows": ("fromless-count",),
    "fromless_where_ignored": ("fromless-where-false",), "fromless_star_accepted": ("fromless-star",),
}
"""The authored case of `conformance.authored_fromless` that each mutant changes."""

GUARDS: dict[str, str] = {
    "fromless_no_row": "rule:Query.source", "fromless_two_rows": "rule:Query.source",
    "fromless_where_ignored": "rule:resolveSelect", "fromless_star_accepted": "rule:resolveResultColumn",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
