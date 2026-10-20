"""Mutants of `printf` and `format` (ADR 0015, slice 6).

The task of slice 6 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_printf`.
"""

from conformance.resolve_mutants import SQLITE

NUMBERS = SQLITE + "Functions/PrintfNumbers.lean"
"""The number fields of printf."""
TEXT = SQLITE + "Functions/PrintfText.lean"
"""The text fields of printf."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "integer_ignores_sign_flag": (NUMBERS,
        "      (if value < 0 then (value.natAbs, [45]) else (value.toNat, if spec.signFlag == 0 then [] else "
        "[spec.signFlag]))\n",
        "      (if value < 0 then (value.natAbs, [45]) else (value.toNat, []))\n"),
    "general_keeps_zeros": (NUMBERS,
        "      else (DoubleForm.fixed, (precision - exponent).toNat, !spec.alternate)\n",
        "      else (DoubleForm.fixed, (precision - exponent).toNat, Bool.false)\n"),
    "quote_not_doubled": (TEXT,
        "    if byte == quote then [byte, byte]\n",
        "    if byte == quote then [byte]\n"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 6: `%d` without the sign flag, `%g` that keeps
trailing zeros, and `%q` that does not double quotes."""

TARGETS: dict[str, tuple[str, ...]] = {
    "integer_ignores_sign_flag": ("printf-integers",),
    "general_keeps_zeros": ("printf-doubles",),
    "quote_not_doubled": ("printf-text",),
}
"""The authored case of `conformance.authored_printf` that each mutant changes."""

GUARDS: dict[str, str] = {
    "integer_ignores_sign_flag": "rule:integerField",
    "general_keeps_zeros": "rule:doubleDigits",
    "quote_not_doubled": "rule:escapeBody",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
