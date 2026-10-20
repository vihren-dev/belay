"""Mutants of subqueries (ADR 0018, slice 1).

The task of slice 1 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_subqueries`.
"""

from conformance.resolve_mutants import SQLITE

EVALUATION = SQLITE + "ExprEval.lean"
"""The evaluation of expressions, with `IN` of a subquery and the scalar subquery."""
SUBQUERIES = SQLITE + "Subqueries.lean"
"""The run of a subquery for an outer row."""
SCOPE = SQLITE + "Resolution/Scope.lean"
"""The resolution of names over the scopes of a query and the queries around it."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "not_in_ignores_null": (EVALUATION,
        "  else if candidates.any (·.isNull) then .null\n",
        "  else if false then .null\n"),
    "outer_row_dropped": (SUBQUERIES,
        "  let cells := outer ++ List.replicate (query.outer - outer.length) .null\n",
        "  let cells := List.replicate query.outer .null\n"),
    "scalar_last_row": (EVALUATION,
        "    ((run.rows.head?.bind List.head?).getD .null, if run.firstCertain then run.fault else .may)\n",
        "    ((run.rows.getLast?.bind List.head?).getD .null, if run.firstCertain then run.fault else .may)\n"),
    "outer_name_first": (SCOPE,
        "  (((List.range scope.depths).map (scope.resolveAt name)).find? (· != .missing)).getD .missing\n",
        "  (((List.range scope.depths).reverse.map (scope.resolveAt name)).find? (· != .missing)).getD .missing\n"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 1: `NOT IN` that ignores a NULL in the
subquery, a correlated reference that does not read the outer row, and a scalar subquery that
gives its last row; and a name that resolves in an outer query before its own."""

TARGETS: dict[str, tuple[str, ...]] = {
    "not_in_ignores_null": ("subquery-in-nulls",),
    "outer_row_dropped": ("subquery-exists-correlated",),
    "scalar_last_row": ("subquery-scalar-first-row",),
    "outer_name_first": ("subquery-own-name-first",),
}
"""The authored case of `conformance.authored_subqueries` that each mutant changes."""

GUARDS: dict[str, str] = {
    "not_in_ignores_null": "rule:inValue",
    "outer_row_dropped": "rule:Query.sourceAfter",
    "scalar_last_row": "rule:Expr.evaluate",
    "outer_name_first": "rule:Scope.resolveName",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
