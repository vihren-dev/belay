"""Mutants of unique key values (ADR 0012, amendment 4, slice 5a).

The task of slice 5a lists the changes that the conformance suite must notice. Each
mutant is one text change in a copy of the model, which
`conformance.resolve_mutants.measure` builds and runs against its target case of
`conformance.authored_keys`.
"""

from conformance.resolve_mutants import SQLITE

LITERAL_DATA = SQLITE + "LiteralData.lean"
"""The key equality of the execution semantics."""

BODY = "  first != .null && second != .null && compareValues first second == .eq"
"""The body of `keyCellsEqual`."""

FOLD = "(fun b => if 65 ≤ b && b ≤ 90 then b + 32 else b)"
"""ASCII lower case of one byte."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "key_text_without_case": (LITERAL_DATA, BODY,
        "  first != .null && second != .null && (match first, second with\n"
        f"    | .text a, .text b => a.map {FOLD} == b.map {FOLD}\n"
        "    | _, _ => compareValues first second == .eq)"),
    "storage_classes_ignored": (LITERAL_DATA, BODY,
        "  first != .null && second != .null && first.scaled == second.scaled && first.bytes == second.bytes"),
    "integer_real_unequal": (LITERAL_DATA, BODY,
        BODY + " && (match first, second with\n"
        "    | .integer _, .real _ | .real _, .integer _ => false\n"
        "    | _, _ => true)"),
    "null_cells_equal": (LITERAL_DATA, BODY, "  (first == .null && second == .null) ||\n" + BODY),
    "first_key_column_only": (LITERAL_DATA,
        "    key.terms.all fun term => match termValue first term, termValue second term with",
        "    (key.terms.take 1).all fun term => match termValue first term, termValue second term with"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the
replacement. The names follow the list in the task of slice 5a: TEXT compared without
ASCII case; values of different storage classes compared by number and bytes only;
an integer and a real never equal; NULL cells equal; only the first column of a key
compared."""

TARGETS: dict[str, tuple[str, ...]] = {
    "key_text_without_case": ("key-text-case",), "storage_classes_ignored": ("key-untyped-classes",),
    "integer_real_unequal": ("key-untyped-real",), "null_cells_equal": ("key-composite-null",),
    "first_key_column_only": ("key-composite-null",),
}
"""The authored case of `conformance.authored_keys` that each mutant changes."""

GUARDS: dict[str, str] = {
    "key_text_without_case": "rule:keyCellsEqual", "storage_classes_ignored": "rule:keyCellsEqual",
    "integer_real_unequal": "rule:keyCellsEqual", "null_cells_equal": "rule:keyCellsEqual",
    "first_key_column_only": "rule:keyEqual",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
