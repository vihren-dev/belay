"""Mutants of the admission obligations, and the evidence for each obligation conjunct.

The verification target admits a write only when `LiteralData.insertReady` or
`LiteralData.updateReady` holds, through `statementReady` (`SqlExecution.lean`). Each
conjunct either keeps a state out of the model that the model would describe wrongly,
or repeats a guarantee made elsewhere. `OBLIGATIONS` lists the conjuncts. A conjunct
that a native state can violate after resolution has a mutant that removes it and a
boundary case of `conformance.authored_obligations`: with the conjunct the case is
`MODEL_UNSUPPORTED`, without it the case disagrees with native SQLite. Every other
conjunct names in `COVERED_ELSEWHERE` what keeps such states out before the obligation
is checked. The mutants run in the scheduled suite (owner decision of 2026-10-14).
"""

from conformance.resolve_mutants import SQLITE

LITERAL_DATA = SQLITE + "LiteralData.lean"
"""The admission obligations of literal writes."""
EXECUTION = SQLITE + "SqlExecution.lean"
"""The admission obligation of each statement."""

OBLIGATIONS: dict[str, tuple[str, str, str]] = {
    "insert-table-ready": (LITERAL_DATA, "insertReady", "tableReady keys table"),
    "insert-row-width": (LITERAL_DATA, "insertReady", "values.length == table.shape.columns.length"),
    "insert-lossless": (LITERAL_DATA, "insertReady",
                        "(table.shape.columns.zip values).all (fun (column, value) => lossless column.affinity value)"),
    "insert-key-values": (LITERAL_DATA, "insertReady",
                          "keys.all (·.all fun position => (values[position]?).any integerOrNull)"),
    "insert-rowid-bounded": (LITERAL_DATA, "insertReady",
                             "(inserted table rows).rows.all (fun row => boundedInteger row.rowid)"),
    "update-filter-comparable": (LITERAL_DATA, "updateReady", "comparisonReady table position"),
    "update-filter-integer": (LITERAL_DATA, "updateReady", "| .integer number => boundedInteger number"),
    "update-table-ready": (LITERAL_DATA, "updateReady", "tableReady keys table"),
    "update-lossless": (LITERAL_DATA, "updateReady",
                        "(table.shape.columns[position]?).any fun column => lossless column.affinity value"),
    "update-keys-after": (LITERAL_DATA, "updateReady",
                          "keys.all (·.all (comparisonReady (updated table assignments filter)))"),
    "create-table-plain": (EXECUTION, "statementReady", "table.plain"),
    "add-column-plain": (EXECUTION, "statementReady", "column.plain"),
    "create-index-refused": (EXECUTION, "statementReady", "| .createIndex .. => false"),
}
"""Each conjunct of the admission obligations: the file under `packages/`, the declaration
that contains it, and its exact text there."""

COVERED_ELSEWHERE: dict[str, str] = {
    "insert-row-width": "reason:resolution gives one value per column (RowSpec.fullRow_rowWidth)",
    "insert-lossless": "restriction:affinity-conversion",
    "insert-key-values": "restriction:key-value",
    "insert-rowid-bounded": "reason:after the largest rowid SQLite chooses a random rowid, so a native "
                            "record of the boundary cannot be replayed exactly",
    "update-filter-integer": "restriction:non-integer-filter",
    "update-lossless": "restriction:affinity-conversion",
    "update-table-ready": "reason:overlaps update-keys-after, which checks every key cell after the update, "
                          "and SQLite guarantees the constraints; update_without_key_checks removes both",
    "create-table-plain": "restriction:create-table-constraints",
    "add-column-plain": "restriction:add-column-constraint",
    "create-index-refused": "restriction:create-index-runs",
}
"""For each conjunct without a mutant: `restriction:ID`, the restriction that resolution
reports before the obligation is checked, or `reason:` and why no boundary case exists."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "insert_without_table_ready": (LITERAL_DATA, "  tableReady keys table &&\n  rows.all", "  rows.all"),
    "update_without_key_checks": (LITERAL_DATA,
        "  tableReady keys table &&\n  assignments.all (fun (position, value) =>\n"
        "    (table.shape.columns[position]?).any fun column => lossless column.affinity value) &&\n"
        "  keys.all (·.all (comparisonReady (updated table assignments filter)))",
        "  assignments.all (fun (position, value) =>\n"
        "    (table.shape.columns[position]?).any fun column => lossless column.affinity value)"),
    "update_filter_without_comparable": (LITERAL_DATA,
        "filter.all (fun (position, value) => comparisonReady table position && match value with",
        "filter.all (fun (position, value) => match value with"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement,
which removes the conjunct that its guard names. Each of the two key checks of
`updateReady` covers the cells that the other checks, so `update_without_key_checks`
removes both."""

TARGETS: dict[str, tuple[str, ...]] = {
    "insert_without_table_ready": ("insert-key-real-equals-integer",),
    "update_without_key_checks": ("update-key-real-equals-integer",),
    "update_filter_without_comparable": ("update-filter-real-equals-integer",),
}
"""The boundary case of `conformance.authored_obligations` that each mutant changes."""

GUARDS: dict[str, str] = {
    "insert_without_table_ready": "obligation:insert-table-ready",
    "update_without_key_checks": "obligation:update-keys-after",
    "update_filter_without_comparable": "obligation:update-filter-comparable",
}
"""The obligation conjunct that each mutant removes. `conformance.mutant_guards` checks every entry."""
