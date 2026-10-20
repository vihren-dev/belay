"""Mutants of the text and type functions and of LIKE (ADR 0015, slice 1).

The task of slice 1 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_text_functions`.
"""

from conformance.resolve_mutants import SQLITE

SCALAR = SQLITE + "Functions/Scalar.lean"
"""The values of the scalar functions."""
TEXT = SQLITE + "Functions/Text.lean"
"""The text functions."""
PATTERN = SQLITE + "Functions/Pattern.lean"
"""The pattern dialects of LIKE and GLOB."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "length_counts_bytes": (SCALAR, "    | .text bytes => .integer (utf8Length bytes)",
                            "    | .text bytes => .integer bytes.length"),
    "lower_changes_non_ascii": (TEXT,
        "def lowerByte (byte : UInt8) : UInt8 := if 65 ≤ byte && byte ≤ 90 then byte + 32 else byte",
        "def lowerByte (byte : UInt8) : UInt8 := if (65 ≤ byte && byte ≤ 90) || 192 ≤ byte then byte + 32 else byte"),
    "like_compares_case": (PATTERN,
        "def likeDialect : PatternDialect := { matchAll := 37, matchOne := 95, matchSet := 0, noCase := true }",
        "def likeDialect : PatternDialect := { matchAll := 37, matchOne := 95, matchSet := 0, noCase := false }"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 1: `length` that counts bytes in text, `lower`
that changes non-ASCII bytes, and `LIKE` that compares case."""

TARGETS: dict[str, tuple[str, ...]] = {
    "length_counts_bytes": ("function-length",),
    "lower_changes_non_ascii": ("function-lower-upper",),
    "like_compares_case": ("function-like-case",),
}
"""The authored case of `conformance.authored_text_functions` that each mutant changes."""

GUARDS: dict[str, str] = {
    "length_counts_bytes": "rule:ScalarFunction.apply",
    "lower_changes_non_ascii": "rule:lowerByte",
    "like_compares_case": "rule:likeDialect",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
