"""Mutants of the table rebuild: a rename of the new table onto the name of the dropped table, which the keys of the
children name (ADR 0019, D4, part 3)."""

from conformance.resolve_mutants import SQLITE

MUTANTS: dict[str, tuple[str, str, str]] = {
    "rename_keeps_selected_parents": (SQLITE + "Execution.lean",
        "    if database.catalog.sameOutline renamed then .ok { database with catalog := renamed }",
        "    if database.catalog.keepsOutline renamed then .ok { database with catalog := renamed }"),
}
"""One exact change per mutant; each measurement builds only its changed classifier closure."""

TARGETS: dict[str, tuple[str, ...]] = {
    "rename_keeps_selected_parents": ("rebuild-corrected",),
}
"""Native cases that distinguish each changed rule from the original model."""

GUARDS: dict[str, str] = {
    "rename_keeps_selected_parents": "rule:step",
}
"""The model declarations whose meaning each mutant checks."""
