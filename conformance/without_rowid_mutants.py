"""Mutants of `WITHOUT ROWID` tables (ADR 0014, slice 2).

The task of slice 2 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_without_rowid`.
"""

from conformance.resolve_mutants import SQLITE

QUERY_EVAL = SQLITE + "QueryEval.lean"
"""The scan order of a table."""
TABLE_OPTIONS = SQLITE + "Resolution/TableOptions.lean"
"""The catalog rules of the table options, such as `WITHOUT ROWID`."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "without_rowid_insertion_order": (QUERY_EVAL,
        "    stableSort (fun a b => (compareSort directions (table.keyCells a) (table.keyCells b)).isLE) table.rows",
        "    table.rows"),
    "without_rowid_null_key": (TABLE_OPTIONS,
        "    if table.primaryKey.contains position then { column with notNull := true } else column",
        "    column"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 2: a scan in insertion order, and a key
column that admits NULL."""

TARGETS: dict[str, tuple[str, ...]] = {
    "without_rowid_insertion_order": ("without-rowid-insert-order",),
    "without_rowid_null_key": ("without-rowid-null-key",),
}
"""The authored case of `conformance.authored_without_rowid` that each mutant changes."""

GUARDS: dict[str, str] = {
    "without_rowid_insertion_order": "rule:_root_.Belay.Sqlite.Model.Table.scanRows",
    "without_rowid_null_key": "rule:CatalogTable.asWithoutRowid",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
