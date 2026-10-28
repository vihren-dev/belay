"""Mutants of ALTER TABLE RENAME TO and RENAME COLUMN: the foreign keys that follow a rename, the check of the
new catalog, the name of the renamed table, the rows, the phase of a dependent object's error and the guard
of the run (ADR 0019, D4, part 2)."""

from conformance.resolve_mutants import SQLITE

CONFORMANCE = "verifier-conformance/VerifierConformance/"

MUTANTS: dict[str, tuple[str, str, str]] = {
    "parent_column_not_followed": (SQLITE + "Resolution/RenameTables.lean",
        "  if key.table.sameName parent then\n    { key with referenced",
        "  if false then\n    { key with referenced"),
    "parent_table_not_followed": (SQLITE + "Resolution/RenameTables.lean",
        "  if key.table.sameName old then { key with table := new } else key",
        "  key"),
    "duplicate_column_unchecked": (SQLITE + "Resolution/RenameCatalog.lean",
        "    | some column => throw (.prepare (.dependentObject .table object.name .afterRename (.expression (.duplicateColumn column))))",
        "    | some _ => pure ()"),
    "dependent_error_in_prepare_phase": (CONFORMANCE + "Case.lean",
        "some (if error.reportedWhileRunning then .step else .prepare)",
        "some .prepare"),
    "taken_name_ignored": (SQLITE + "Resolution/Renames.lean",
        "      if catalog.nameTaken newName then prepareError catalog (.renameTargetTaken newName)\n      else if reservedName target.name",
        "      if false then prepareError catalog (.renameTargetTaken newName)\n      else if reservedName target.name"),
    "table_keeps_old_name": (SQLITE + "Resolution/RenameCatalog.lean",
        "      | some renamed => pure { name := match request.target with\n          | .table _ => request.new",
        "      | some renamed => pure { name := match request.target with\n          | .table _ => object.name"),
    "rewrite_always_rejected": (SQLITE + "Execution.lean",
        "    if database.catalog.sameOutline renamed then .ok { database with catalog := renamed }",
        "    if false then .ok { database with catalog := renamed }"),
    "rewrite_loses_rows": (SQLITE + "Execution.lean",
        "    if database.catalog.sameOutline renamed then .ok { database with catalog := renamed }",
        "    if database.catalog.sameOutline renamed then .ok { catalog := renamed, rows := database.rows.map fun _ => [] }"),
}
"""One exact change per mutant; each measurement builds only its changed classifier closure."""

TARGETS: dict[str, tuple[str, ...]] = {
    "parent_column_not_followed": ("rename-column-parent",),
    "parent_table_not_followed": ("rename-table-parent",),
    "duplicate_column_unchecked": ("rename-column-duplicate",),
    "dependent_error_in_prepare_phase": ("rename-column-duplicate",),
    "taken_name_ignored": ("rename-table-index-name-taken",),
    "table_keeps_old_name": ("rename-table-rows",),
    "rewrite_always_rejected": ("rename-table-rows",),
    "rewrite_loses_rows": ("rename-table-rows",),
}
"""Native cases that distinguish each changed rule from the original model."""

GUARDS: dict[str, str] = {
    "parent_column_not_followed": "rule:ForeignKey.renameParentColumn",
    "parent_table_not_followed": "rule:ForeignKey.renameParent",
    "duplicate_column_unchecked": "rule:checkRenamedObject",
    "dependent_error_in_prepare_phase": "rule:errorPhase",
    "taken_name_ignored": "rule:resolveRenameTable",
    "table_keeps_old_name": "rule:renameObject",
    "rewrite_always_rejected": "rule:step",
    "rewrite_loses_rows": "rule:step",
}
"""The model declarations whose meaning each mutant checks."""
