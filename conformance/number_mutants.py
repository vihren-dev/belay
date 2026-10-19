"""Mutants of the number rules of queries (ADR 0012, slice 2).

The task of slice 2 lists the changes that the conformance suite must notice. Each
mutant is one text change in a copy of the model, which
`conformance.resolve_mutants.measure` builds and runs against the authored number
cases of `conformance.authored_numbers`, together with the query cases of slice 1.
"""

from conformance.resolve_mutants import SQLITE

ARITHMETIC = SQLITE + "Arithmetic.lean"
"""Arithmetic and CAST of values."""
SUMMATION = SQLITE + "Summation.lean"
"""SUM and AVG."""
NUMBER_TEXT = SQLITE + "NumberText.lean"
"""The parse of text to numbers."""
VALUES = SQLITE + "ExprEval.lean"
"""The value and fault of an expression over one row."""
EXPRESSIONS = SQLITE + "Resolution/QueryExprs.lean"
"""Resolution of query expressions."""
FORMS = SQLITE + "Resolution/ExprForms.lean"
"""The call and condition forms of expression resolution."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "overflow_stays_integer": (ARITHMETIC,
        "if fitsInt64Range result then Value.integer result else operator.real left right", "Value.integer result"),
    "integer_division_as_real": (ARITHMETIC,
        "  | .divide => if b == 0 then .null else exact (a.tdiv b)", "  | .divide => if b == 0 then .null else operator.real left right"),
    "real_division_by_zero_not_null": (ARITHMETIC,
        "  | .divide => if b == 0 then .null else realValue (a / b)", "  | .divide => realValue (a / b)"),
    "nan_not_null": (ARITHMETIC,
        "def realValue (value : Float) : Value := if value.isNaN then .null else .real value.toBits",
        "def realValue (value : Float) : Value := .real value.toBits"),
    "real_remainder_in_doubles": (ARITHMETIC,
        "    else realValue (Float.ofInt (left.toInt64.tmod (if divisor == -1 then 1 else divisor)))",
        "    else realValue (a - b * (a / b).floor)"),
    "cast_integer_rounds": (ARITHMETIC,
        "  | .real bits => realToI64 (Float.ofBits bits)", "  | .real bits => realToI64 (Float.ofBits bits).round"),
    "sum_naive": (SUMMATION,
        "  let error := if state.sum.abs > value.abs then state.error + ((state.sum - total) + value)\n"
        "    else state.error + ((value - total) + state.sum)", "  let error := state.error"),
    "sum_overflow_ignored": (SUMMATION, "  else if state.overflow then none", "  else if false then none"),
    "avg_integer": (SUMMATION,
        "    realValue (total / Float.ofNat state.count)", "    .integer (realToI64 (total / Float.ofNat state.count))"),
    "coalesce_last": (VALUES,
        "    (if value.isNullCell then other else value, (fault.join later).soften)",
        "    (if other.isNullCell then value else other, (fault.join later).soften)"),
    "spaces_not_skipped": (NUMBER_TEXT,
        "def dropSpaces (bytes : List UInt8) : List UInt8 := bytes.dropWhile isSpaceByte",
        "def dropSpaces (bytes : List UInt8) : List UInt8 := bytes"),
    "exponent_ignored": (NUMBER_TEXT, "    if marker == 101 || marker == 69 then", "    if false then"),
    "coalesce_argument_count_removed": (FORMS,
        "  if normalizeIdentifier name == \"coalesce\" then .prepare (.wrongArgumentCount name) else unmodeledFunction",
        "  unmodeledFunction"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the
replacement. The names follow the list in the task of slice 2."""

TARGETS: dict[str, tuple[str, ...]] = {
    "overflow_stays_integer": ("add-subtract-multiply-limits",), "integer_division_as_real": ("divide-remainder-limits",),
    "real_division_by_zero_not_null": ("real-arithmetic",), "nan_not_null": ("nan-is-null",),
    "real_remainder_in_doubles": ("real-arithmetic",), "cast_integer_rounds": ("cast-integer",),
    "sum_naive": ("sum-compensated",), "sum_overflow_ignored": ("sum-overflow",), "avg_integer": ("avg-overflow-succeeds",),
    "coalesce_last": ("coalesce",), "spaces_not_skipped": ("text-operands",), "exponent_ignored": ("cast-real",),
    "coalesce_argument_count_removed": ("coalesce-one-argument",),
}
"""The authored case that each mutant changes: the case of
`conformance.authored_numbers` that tests the rule. A mutant copy classifies only its
target, which keeps the measurement short."""

GUARDS: dict[str, str] = {
    "overflow_stays_integer": "rule:ArithmeticOperator.integer",
    "integer_division_as_real": "rule:ArithmeticOperator.integer",
    "real_division_by_zero_not_null": "rule:ArithmeticOperator.real",
    "nan_not_null": "rule:realValue",
    "real_remainder_in_doubles": "rule:ArithmeticOperator.real",
    "cast_integer_rounds": "rule:Value.toInt64",
    "sum_naive": "rule:SumState.addDouble",
    "sum_overflow_ignored": "rule:SumState.sumValue",
    "avg_integer": "rule:SumState.averageValue",
    "coalesce_last": "rule:Expr.evaluate",
    "spaces_not_skipped": "rule:dropSpaces",
    "exponent_ignored": "rule:atofExponentPart",
    "coalesce_argument_count_removed": "rule:callIssue",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
