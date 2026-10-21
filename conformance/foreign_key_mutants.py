"""Mutants of enforced foreign keys (ADR 0018, slice 4).

The task of slice 4 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_foreign_keys`.
"""

from conformance.resolve_mutants import SQLITE

MATCH = SQLITE + "ForeignKeyMatch.lean"
"""How a child row finds its parent row and a parent row its child rows."""
ROWS = SQLITE + "ForeignKeyRows.lean"
"""The rows of a write that checks foreign keys, with the actions."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "composite_null_checked": (MATCH,
        "  link.key.columns.any fun position => values.getD position .null == .null\n",
        "  link.key.columns.all fun position => values.getD position .null == .null\n"),
    "set_null_deletes": (ROWS,
        "    | .cascade, none => acted <$> run (.delete link.child targets false false true) state\n",
        "    | .cascade, none | .setNull, none => acted <$> run (.delete link.child targets false false true) state\n"),
    "cascade_keeps_old_key": (ROWS,
        "      match actionCells child parent link key (new.getD old) action with\n",
        "      match actionCells child parent link key old action with\n"),
    "lookup_without_affinity": (MATCH,
        "    | some column => LiteralData.keyCellsEqual (row.values.getD position .null) (storeValue (indexAffinity column) value)\n",
        "    | some column => LiteralData.keyCellsEqual (row.values.getD position .null) value\n"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 4: a check of a composite child key with one
NULL column, `SET NULL` that deletes the child row, `CASCADE` on update that keeps the old child
key, and a check that compares the child value without the parent key's affinity."""

TARGETS: dict[str, tuple[str, ...]] = {
    "composite_null_checked": ("composite",),
    "set_null_deletes": ("parent-delete",),
    "cascade_keeps_old_key": ("parent-update",),
    "lookup_without_affinity": ("affinity",),
}
"""The authored case of `conformance.authored_foreign_keys` that each mutant changes."""

GUARDS: dict[str, str] = {
    "composite_null_checked": "rule:ForeignKeyLink.hasNull",
    "set_null_deletes": "rule:runAction",
    "cascade_keeps_old_key": "rule:runAction",
    "lookup_without_affinity": "rule:indexHolds",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
