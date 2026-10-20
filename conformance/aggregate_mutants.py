"""Mutants of the aggregates `group_concat`, `string_agg` and `total` (ADR 0015, slice 5).

The task of slice 5 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_aggregates`.
"""

from conformance.resolve_mutants import SQLITE

EVAL = SQLITE + "QueryEval.lean"
"""The values of the aggregates."""
SUMMATION = SQLITE + "Summation.lean"
"""The summation of SUM, AVG and TOTAL."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "separator_always_comma": (EVAL,
        "      | some text => text ++ concatSeparator separator ++ concatText value)) rest\n",
        "      | some text => text ++ concatSeparator none ++ concatText value)) rest\n"),
    "concat_keeps_null": (EVAL,
        "    if value.isNull then concatRows text rest\n",
        "    if value.isNull && false then concatRows text rest\n"),
    "total_null_when_empty": (SUMMATION,
        "  realValue (if state.approximate then state.approximateTotal else Float.ofInt state.integerSum)\n",
        "  if state.count == 0 then .null\n"
        "  else realValue (if state.approximate then state.approximateTotal else Float.ofInt state.integerSum)\n"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 5: a separator argument that is ignored,
`group_concat` that keeps a NULL value as empty text, and `total` that gives NULL for an
empty group."""

TARGETS: dict[str, tuple[str, ...]] = {
    "separator_always_comma": ("aggregate-group-concat",),
    "concat_keeps_null": ("aggregate-group-concat",),
    "total_null_when_empty": ("aggregate-total",),
}
"""The authored case of `conformance.authored_aggregates` that each mutant changes."""

GUARDS: dict[str, str] = {
    "separator_always_comma": "rule:concatRows",
    "concat_keeps_null": "rule:concatRows",
    "total_null_when_empty": "rule:SumState.totalValue",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
