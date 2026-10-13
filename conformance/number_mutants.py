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
EVALUATION = SQLITE + "QueryEval.lean"
"""Evaluation of query expressions."""
EXPRESSIONS = SQLITE + "Resolution/QueryExprs.lean"
"""Resolution of query expressions."""

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
    "coalesce_last": (EVALUATION,
        "    if value.isNullCell then rest.eval row else value",
        "    let other := rest.eval row\n    if other.isNullCell then value else other"),
    "spaces_not_skipped": (NUMBER_TEXT,
        "def dropSpaces (bytes : List UInt8) : List UInt8 := bytes.dropWhile isSpaceByte",
        "def dropSpaces (bytes : List UInt8) : List UInt8 := bytes"),
    "exponent_ignored": (NUMBER_TEXT, "    if marker == 101 || marker == 69 then", "    if false then"),
    "coalesce_argument_count_removed": (EXPRESSIONS,
        "  if normalizeIdentifier name == \"coalesce\" then .prepare (.wrongArgumentCount name) else unmodeledFunction",
        "  unmodeledFunction"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the
replacement. The names follow the list in the task of slice 2."""
