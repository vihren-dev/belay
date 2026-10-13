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
        "let grouped := if query.groupBy.isEmpty then [rows] else",
        "let grouped := if query.groupBy.isEmpty then (if rows.isEmpty then [] else [rows]) else"),
    "limit_one_too_high": (EVALUATION, "window.take limit", "window.take (limit + 1)"),
    "offset_ignored": (EVALUATION, "let window := sorted.drop query.offset", "let window := sorted"),
    "no_such_column": (EXPRESSIONS,
        "      else .error (.prepare (.noSuchColumn name))", "      else .ok (.literal .null, none)"),
    "no_such_table": (RESOLUTION,
        "    else prepareError catalog (.noSuchTable tableName)", "    else restrict index [1] \"mutant\""),
    "no_misuse_of_aggregate": (EXPRESSIONS,
        "  if misuse then .prepare (.misuseOfAggregate function)", "  if false then .prepare (.misuseOfAggregate function)"),
    "no_aggregate_in_group_by": (RESOLUTION,
        ".error (if aggregateCall term then .prepare .aggregateInGroupBy else (callIssue name).under [3, item])",
        ".error ((callIssue name).under [3, item])"),
    "no_order_by_out_of_range": (RESOLUTION,
        "      | some (.error ()) => .error (.prepare (.orderByOutOfRange (item + 1) outputs.length))",
        "      | some (.error ()) => .error (.restriction [4, item] \"mutant\")"),
    "no_group_by_out_of_range": (RESOLUTION,
        "        | some (.error ()) => .error (.prepare (.groupByOutOfRange (item + 1) outputs.length))",
        "        | some (.error ()) => .error (.restriction [3, item] \"mutant\")"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the
replacement. The names follow the list of ADR 0012, "Testing"."""
