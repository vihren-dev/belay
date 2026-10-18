"""Mutants of query semantics and resolution (ADR 0012, slice 1, "Testing").

ADR 0012 requires that each listed change of the query rules makes at least one
conformance case change its verdict, so that the suite is known to test each rule.
Each mutant is one text change in a copy of the model, which
`conformance.resolve_mutants.measure` builds and runs against the authored query
cases of `conformance.authored_queries`. A removed prepare error becomes a model
restriction or lets the query run, so the case no longer agrees.
"""

from conformance.resolve_mutants import SQLITE

COMPARISON = SQLITE + "Comparison.lean"
"""The Values level: the comparison of two values."""
EVALUATION = SQLITE + "QueryEval.lean"
"""The Expressions and Queries levels: evaluation and the query steps."""
RESOLUTION = SQLITE + "Resolution/Queries.lean"
"""The resolution of a SELECT."""
EXPRESSIONS = SQLITE + "Resolution/QueryExprs.lean"
"""The resolution of query expressions."""
FORMS = SQLITE + "Resolution/ExprForms.lean"
"""The call and condition forms of expression resolution."""
SOURCES = SQLITE + "Resolution/Sources.lean"
"""The resolution of the tables of FROM."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "null_equals_null": (COMPARISON,
        "  | .is | .isNot =>\n    if left.isNull || right.isNull then truth ((left.isNull && right.isNull) == (operator == .is))\n"
        "    else truth (operator.holds (compareValues left right))\n  | .eq | .ne",
        "  | .is | .isNot | .eq =>\n    if left.isNull || right.isNull then truth ((left.isNull && right.isNull) == (operator != .isNot))\n"
        "    else truth (operator.holds (compareValues left right))\n  | .ne"),
    "integer_as_double": (COMPARISON,
        "  | .integer value => value * 2 ^ 1074", "  | .integer value => (realScaled (Float.ofInt value).toBits).getD 0"),
    "text_without_case": (COMPARISON,
        "  | .text bytes | .blob bytes => bytes",
        "  | .text bytes => bytes.map fun byte => if 65 ≤ byte ∧ byte ≤ 90 then byte + 32 else byte\n  | .blob bytes => bytes"),
    "descending_ignored": (EVALUATION,
        "if descending then compareValues b a else compareValues a b", "compareValues a b"),
    "null_last_ascending": (EVALUATION,
        "if descending then compareValues b a else compareValues a b",
        "if descending then compareValues b a\n  else if a.isNull != b.isNull then (if a.isNull then .gt else .lt) else compareValues a b"),
    "count_counts_null": (EVALUATION,
        "  | .count operand => .integer (rows.filter fun row => !(operand.eval row).isNull).length",
        "  | .count _ => .integer rows.length"),
    "extremum_over_null": (EVALUATION, "(values.filter (!·.isNull)).foldl", "values.foldl"),
    "empty_aggregate_no_row": (EVALUATION,
        "  if query.groupBy.isEmpty then [rows] else groups query.groupBy rows",
        "  if query.groupBy.isEmpty then (if rows.isEmpty then [] else [rows]) else groups query.groupBy rows"),
    "limit_one_too_high": (EVALUATION, "window.take limit", "window.take (limit + 1)"),
    "offset_ignored": (EVALUATION, "let window := sorted.drop query.offset", "let window := sorted"),
    "no_such_column": (EXPRESSIONS,
        "      else .error (.prepare (.noSuchColumn name))", "      else .ok (.literal .null, none)"),
    "no_such_table": (SOURCES,
        "    else .error (.prepare (.noSuchTable reference.table))", "    else .error (.restriction path .systemTable)"),
    "no_misuse_of_aggregate": (FORMS,
        "  if misuse then .prepare (.misuseOfAggregate function)", "  if false then .prepare (.misuseOfAggregate function)"),
    "no_aggregate_in_group_by": (RESOLUTION,
        ".error (if aggregateCall term then .prepare .aggregateInGroupBy else (callIssue name).under [4, item])",
        ".error ((callIssue name).under [4, item])"),
    "no_order_by_out_of_range": (RESOLUTION,
        "      | some (.error ()) => .error (.prepare (.orderByOutOfRange (item + 1) outputs.length))",
        "      | some (.error ()) => .error (.restriction [4, item] .aggregateOrderBy)"),
    "no_group_by_out_of_range": (RESOLUTION,
        "        | some (.error ()) => .error (.prepare (.groupByOutOfRange (item + 1) outputs.length))",
        "        | some (.error ()) => .error (.restriction [3, item] .groupByTerm)"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the
replacement. The names follow the list of ADR 0012, "Testing"."""

TARGETS: dict[str, tuple[str, ...]] = {
    "null_equals_null": ("compare-null-operands",), "integer_as_double": ("integer-real-exact",),
    "text_without_case": ("text-binary",), "descending_ignored": ("order-descending",),
    "null_last_ascending": ("order-storage-classes",), "count_counts_null": ("count-skips-null",),
    "extremum_over_null": ("min-max-skip-null",), "empty_aggregate_no_row": ("aggregate-empty-table",),
    "limit_one_too_high": ("limit-offset",), "offset_ignored": ("limit-offset",),
    "no_such_column": ("no-such-column",), "no_such_table": ("no-such-table",),
    "no_misuse_of_aggregate": ("aggregate-in-where",), "no_aggregate_in_group_by": ("aggregate-written-in-group-by",),
    "no_order_by_out_of_range": ("order-by-out-of-range",), "no_group_by_out_of_range": ("group-by-out-of-range",),
}
"""The authored case that each mutant changes: the case of
`conformance.authored_queries` that tests the rule. A mutant copy classifies only its
target, which keeps the measurement short."""

GUARDS: dict[str, str] = {
    "null_equals_null": "rule:Comparison.apply",
    "integer_as_double": "rule:Value.scaled",
    "text_without_case": "rule:Value.bytes",
    "descending_ignored": "rule:compareTerm",
    "null_last_ascending": "rule:compareTerm",
    "count_counts_null": "rule:Aggregate.eval",
    "extremum_over_null": "rule:extremum",
    "empty_aggregate_no_row": "rule:queryGroups",
    "limit_one_too_high": "rule:Query.run",
    "offset_ignored": "rule:Query.run",
    "no_such_column": "rule:resolveOperand",
    "no_such_table": "rule:resolveTableReference",
    "no_misuse_of_aggregate": "rule:aggregateIssue",
    "no_aggregate_in_group_by": "rule:resolveSelect",
    "no_order_by_out_of_range": "rule:resolveSelect",
    "no_group_by_out_of_range": "rule:resolveSelect",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
