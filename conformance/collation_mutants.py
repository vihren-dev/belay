"""Mutants of collations (ADR 0014, slice 3).

The task of slice 3 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_collations`.
"""

from conformance.resolve_mutants import SQLITE

COMPARISON = SQLITE + "Comparison.lean"
"""The comparison operators."""
COLLATIONS = SQLITE + "Resolution/Collations.lean"
"""The collation that resolution decides for a comparison."""
LITERAL_DATA = SQLITE + "LiteralData.lean"
"""The key equality of the execution semantics."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "comparison_ignores_collation": (COMPARISON,
        "    if left.isNull || right.isNull then .null else truth (operator.holds (collation.compare left right))",
        "    if left.isNull || right.isNull then .null else truth (operator.holds (compareValues left right))"),
    "right_collation_first": (COLLATIONS,
        "  (left.explicitCollation <|> right.explicitCollation <|> left.columnCollation scope <|>\n"
        "    right.columnCollation scope).getD .binary",
        "  (right.explicitCollation <|> left.explicitCollation <|> right.columnCollation scope <|>\n"
        "    left.columnCollation scope).getD .binary"),
    "key_compares_binary": (LITERAL_DATA,
        "      | some a, some b => keyCellsEqual a b term.collation", "      | some a, some b => keyCellsEqual a b"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 3: a comparison that ignores the collation,
the right operand's collation chosen first, and a key that compares with `BINARY`."""

TARGETS: dict[str, tuple[str, ...]] = {
    "comparison_ignores_collation": ("collate-nocase-column",),
    "right_collation_first": ("collate-column-left",),
    "key_compares_binary": ("collate-unique-column",),
}
"""The authored case of `conformance.authored_collations` that each mutant changes."""

GUARDS: dict[str, str] = {
    "comparison_ignores_collation": "rule:Comparison.apply",
    "right_collation_first": "rule:comparisonCollation",
    "key_compares_binary": "rule:keyEqual",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
