"""Mutants of the exact numeric functions (ADR 0015, slice 2).

The task of slice 2 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_numeric_functions`.
"""

from conformance.resolve_mutants import SQLITE

NUMERIC = SQLITE + "Functions/Numeric.lean"
"""The numeric functions."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "round_half_even": (NUMERIC,
        "    else if count == 0 then realValue (Float.ofInt (double + (if double < 0 then -0.5 else 0.5)).toInt64.toInt)",
        "    else if count == 0 then realValue (Float.ofInt (if (double - Float.ofInt double.toInt64.toInt).abs == 0.5 "
        "&& double.toInt64.toInt % 2 == 0 then double else double + (if double < 0 then -0.5 else 0.5)).toInt64.toInt)"),
    "floor_truncates": (NUMERIC,
        "    withZeroSign value (if truncated > value then truncated - 1 else truncated)",
        "    withZeroSign value truncated"),
    "mod_keeps_integer": (NUMERIC,
        "  | some x, some y => realValue (modDouble x.toReal y.toReal)",
        "  | some x, some y => match x, y with\n"
        "    | .integer a, .integer b => if b == 0 then .null else .integer (a.tmod b)\n"
        "    | _, _ => realValue (modDouble x.toReal y.toReal)"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 2: `round` that rounds half to even, `floor`
that truncates toward zero, and `mod` that keeps an integer result for integers."""

TARGETS: dict[str, tuple[str, ...]] = {
    "round_half_even": ("numeric-round",),
    "floor_truncates": ("numeric-floor-ceil-trunc",),
    "mod_keeps_integer": ("numeric-mod",),
}
"""The authored case of `conformance.authored_numeric_functions` that each mutant changes."""

GUARDS: dict[str, str] = {
    "round_half_even": "rule:roundValue",
    "floor_truncates": "rule:floorDouble",
    "mod_keeps_integer": "rule:modValue",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
