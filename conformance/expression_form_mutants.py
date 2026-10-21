"""Mutants of the expression forms IN, BETWEEN, CASE and || (ADR 0018, slice 2).

The task of slice 2 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_expression_forms`.
"""

from conformance.resolve_mutants import SQLITE

EXPRESSIONS = SQLITE + "Resolution/QueryExprs.lean"
"""The resolution of query expressions, with the forms of slice 2."""
SCALAR = SQLITE + "Functions/Scalar.lean"
"""The scalar functions, with the operator ||."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "in_list_right_collation": (EXPRESSIONS,
        "    | _, _ => .ok (.inList a.1 resolved a.2 (operand.collationIn scope) negated, none)\n",
        "    | _, _ => .ok (.inList a.1 resolved a.2 ((values.head?.bind (·.columnCollation scope)).getD\n"
        "        (operand.collationIn scope)) negated, none)\n"),
    "between_null_first": (EXPRESSIONS,
        "    let both := Resolved.Expr.and\n",
        "    let both := Resolved.Expr.arithmetic .multiply\n"),
    "case_null_base_matches": (EXPRESSIONS,
        "          .compare .eq (comparisonAffinity value.2 resolved.2) value.1 resolved.1 (comparisonCollation scope written operand)\n",
        "          .compare .is (comparisonAffinity value.2 resolved.2) value.1 resolved.1 (comparisonCollation scope written operand)\n"),
    "pipes_skip_null": (SCALAR,
        "  | .pipes, [left, right] => .ok (if left.isNull || right.isNull then .null else .text (left.textBytes ++ right.textBytes))\n",
        "  | .pipes, [left, right] => .ok (concatValue [] [left, right])\n"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 2: an `IN` list that compares under the
collation of a column on the right, `BETWEEN` that gives NULL when either comparison is NULL,
`CASE` whose NULL base matches a NULL `WHEN`, and `||` that skips a NULL operand."""

TARGETS: dict[str, tuple[str, ...]] = {
    "in_list_right_collation": ("form-in-list-collation",),
    "between_null_first": ("form-between",),
    "case_null_base_matches": ("form-case-base",),
    "pipes_skip_null": ("form-concat",),
}
"""The authored case of `conformance.authored_expression_forms` that each mutant changes."""

GUARDS: dict[str, str] = {
    "in_list_right_collation": "rule:resolveOperand",
    "between_null_first": "rule:resolveOperand",
    "case_null_base_matches": "rule:resolveCase",
    "pipes_skip_null": "rule:ScalarFunction.apply",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
