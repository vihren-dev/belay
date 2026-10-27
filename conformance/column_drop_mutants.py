"""Mutants of ALTER TABLE DROP COLUMN: the checks of SQLite on the column, the schema tests after the edit, the
rows and the guard of the run (ADR 0019, D4, part 3)."""

from conformance.resolve_mutants import SQLITE

MUTANTS: dict[str, tuple[str, str, str]] = {
    "primary_key_drop_allowed": (SQLITE + "Resolution/DropColumnResolve.lean",
        "            if table.primaryKey.contains index || table.rowidAlias == some index then",
        "            if false then"),
    "unique_drop_allowed": (SQLITE + "Resolution/DropColumnResolve.lean",
        "            else if table.inlineUnique.contains index then prepareError",
        "            else if false then prepareError"),
    "last_column_drop_allowed": (SQLITE + "Resolution/DropColumnResolve.lean",
        "            else if table.columns.length ≤ 1 then prepareError",
        "            else if false then prepareError"),
    "index_reading_column_allowed": (SQLITE + "Resolution/DropColumnResolve.lean",
        "    if definition.readsColumn target index then\n      if definition.exactNames",
        "    if false then\n      if definition.exactNames"),
    "generated_dependency_ignored": (SQLITE + "Resolution/DropColumnDependents.lean",
        "(if table.generatedReads index then [.generated] else [])",
        "[]"),
    "check_dependency_ignored": (SQLITE + "Resolution/DropColumnDependents.lean",
        "(if (table.checksAfterDrop index).any (·.condition.readsColumn index) then [.checks] else [])",
        "[]"),
    "drop_loses_rows": (SQLITE + "DatabaseDropColumn.lean",
        "rows := database.rows.modify position (·.map (Row.dropValue index)) }",
        "rows := database.rows.modify position (fun _ => []) }"),
    "drop_keeps_cell": (SQLITE + "DatabaseDropColumn.lean",
        "rows := database.rows.modify position (·.map (Row.dropValue index)) }",
        "rows := database.rows }"),
    "drop_always_rejected": (SQLITE + "Execution.lean",
        "    if database.runsDropColumn target index stored then .ok (database.dropColumn target index stored)",
        "    if false then .ok (database.dropColumn target index stored)"),
}
"""One exact change per mutant; each measurement builds only its changed classifier closure."""

TARGETS: dict[str, tuple[str, ...]] = {
    "primary_key_drop_allowed": ("column-drop-primary-key",),
    "unique_drop_allowed": ("column-drop-unique",),
    "last_column_drop_allowed": ("column-drop-last-column",),
    "index_reading_column_allowed": ("column-drop-index-reads-column",),
    "generated_dependency_ignored": ("column-drop-generated-reads-column",),
    "check_dependency_ignored": ("column-drop-table-check",),
    "drop_loses_rows": ("column-drop-rows",),
    "drop_keeps_cell": ("column-drop-rows",),
    "drop_always_rejected": ("column-drop-rows",),
}
"""Native cases that distinguish each changed rule from the original model."""

GUARDS: dict[str, str] = {
    "primary_key_drop_allowed": "rule:resolveDropColumn",
    "unique_drop_allowed": "rule:resolveDropColumn",
    "last_column_drop_allowed": "rule:resolveDropColumn",
    "index_reading_column_allowed": "rule:checkDroppedObject",
    "generated_dependency_ignored": "rule:CatalogTable.dependencies",
    "check_dependency_ignored": "rule:CatalogTable.dependencies",
    "drop_loses_rows": "rule:Database.dropColumn",
    "drop_keeps_cell": "rule:Database.dropColumn",
    "drop_always_rejected": "rule:step",
}
"""The model declarations whose meaning each mutant checks."""
