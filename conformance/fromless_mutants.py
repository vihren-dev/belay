"""Mutants of queries without FROM (ADR 0012, amendment 5, slice 6a).

The task of slice 6a lists the changes that the conformance suite must notice. Each
mutant is one logical fault in a copy of the model, which
`conformance.resolve_mutants.measure` builds and runs against its target case of
`conformance.authored_fromless`. `conformance.query_mutants` already has the mutant that
gives an aggregate over zero rows no row (`empty_aggregate_no_row`).
"""

from conformance.resolve_mutants import SQLITE
from conformance.mutation_edits import Guard, Mutation, MutationGroup

FUNCTIONS = SQLITE + "QueryFunctions.lean"
"""The source rows of a query, joined from the one row with no cells."""
QUERIES = SQLITE + "Resolution/ResultColumnTraced.lean"
QUERY_BODY = SQLITE + "Resolution/QueryBodyTraced.lean"
"""The resolution of a SELECT."""

MUTANTS: dict[str, Mutation] = {
    "fromless_no_row": (FUNCTIONS, "{ rows := [[]], width := 0, fault := .none }",
        "{ rows := [], width := 0, fault := .none }"),
    "fromless_two_rows": (FUNCTIONS, "{ rows := [[]], width := 0, fault := .none }",
        "{ rows := [[], []], width := 0, fault := .none }"),
    "fromless_where_ignored": (QUERY_BODY,
        "  return ({ sources, filter := condition,",
        "  return ({ sources, filter := if sources.isEmpty then none else condition,"),
    "fromless_star_accepted": MutationGroup((
        (QUERIES, "  | .star => if !(scope.inner.any (·.namesVisible)) then throw (.prepare .noTablesSpecified) else",
         "  | .star => if false then throw (.prepare .noTablesSpecified) else"),
        (SQLITE + "Resolution/CompoundTerms.lean",
         "    | .star => if !(scope.inner.any (·.namesVisible)) then some (.prepare .noTablesSpecified) else none",
         "    | .star => if false then some (.prepare .noTablesSpecified) else none"),
    )),
}
"""Each edit names the file under `packages/`, the exact text and its replacement.
The star fault changes both the early expansion check and result-column resolution.
The names follow the slice 6a task: the source has no row; the source has two rows;
WHERE without FROM is ignored; and `*` without FROM is accepted."""

TARGETS: dict[str, tuple[str, ...]] = {
    "fromless_no_row": ("fromless-values",), "fromless_two_rows": ("fromless-count",),
    "fromless_where_ignored": ("fromless-where-false",), "fromless_star_accepted": ("fromless-star",),
}
"""The authored case of `conformance.authored_fromless` that each mutant changes."""

GUARDS: dict[str, Guard] = {
    "fromless_no_row": "rule:Query.source", "fromless_two_rows": "rule:Query.source",
    "fromless_where_ignored": "rule:resolveQueryBodyTraced", "fromless_star_accepted": ("rule:resolveResultColumnTraced", "rule:starIssue"),
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes, one link per grouped edit. `conformance.mutant_guards` checks every entry."""
