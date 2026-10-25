"""Mutants of `DROP INDEX` and `DROP TABLE` (ADR 0014, slice 7).

The task of slice 7 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_drops`.
"""

from conformance.resolve_mutants import SQLITE

DROPS = SQLITE + "Resolution/Drops.lean"
"""The resolution of DROP TABLE and DROP INDEX."""
CATALOG_DROP = SQLITE + "Resolution/CatalogDrop.lean"
"""The catalog function of a DROP."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "drop_table_keeps_indexes": (DROPS, "      let positions := catalog.tableObjects position",
                                 "      let positions := [position]"),
    "drop_keeps_positions": (CATALOG_DROP,
        "  | .index found => .index { found with table := keptBelow positions found.table }",
        "  | .index found => .index found"),
    "if_exists_reports_missing": (DROPS,
        "      | none => if ifExists then .ok (.drop [], catalog.drop []) else prepareError catalog (.noSuchTable name)",
        "      | none => prepareError catalog (.noSuchTable name)"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 7: a DROP TABLE that keeps the table's
indexes, a DROP that does not move the later positions, and `IF EXISTS` that still reports
`no such table`."""

TARGETS: dict[str, tuple[str, ...]] = {
    "drop_table_keeps_indexes": ("drop-table-index-name-free",),
    "drop_keeps_positions": ("drop-table-later-index",),
    "if_exists_reports_missing": ("drop-table-if-exists",),
}
"""The authored case of `conformance.authored_drops` that each mutant changes."""

GUARDS: dict[str, str] = {
    "drop_table_keeps_indexes": "rule:resolveDropTable",
    "drop_keeps_positions": "rule:CatalogEntry.afterDrop",
    "if_exists_reports_missing": "rule:resolveDropTable",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
