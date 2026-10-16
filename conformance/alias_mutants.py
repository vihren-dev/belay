"""Mutants of rowid aliases (ADR 0012, amendment 4, slice 5b).

The task of slice 5b lists the changes that the conformance suite must notice. Each
mutant is one text change in a copy of the model, which
`conformance.resolve_mutants.measure` builds and runs against its target case of
`conformance.authored_aliases`. `conformance.resolve_mutants` already has the mutant that
treats `INTEGER PRIMARY KEY DESC` as an alias (`desc_rowid_alias`).
"""

from conformance.resolve_mutants import SQLITE

LITERAL_DATA = SQLITE + "LiteralData.lean"
"""The rows that INSERT writes."""
ROW_UPDATE = SQLITE + "RowUpdate.lean"
"""The rows that UPDATE writes."""
DEFINITIONS = SQLITE + "Resolution/Definitions.lean"
"""The resolution of table definitions, which finds the alias."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "null_alias_stays_null": (LITERAL_DATA, "  | some position => values.set position (.integer rowid)",
        "  | some position => values"),
    "non_integer_alias_stored": (LITERAL_DATA, "  | some (.real _) | some (.text _) | some (.blob _) => true",
        "  | some (.real _) | some (.text _) | some (.blob _) => false"),
    "alias_value_not_rowid": (LITERAL_DATA, "  | some (.integer value) => value",
        "  | some (.integer _) => nextRowid table.rows"),
    "update_keeps_rowid": (ROW_UPDATE, "  | some (.integer value) => { row with rowid := value }",
        "  | some (.integer _) => row"),
    "table_constraint_not_alias": (DEFINITIONS,
        "      | [position] => if aliasesRowid (table.columns[position]?.bind (·.declaredType)) then some position else none",
        "      | [_] => none"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the
replacement. The names follow the list in the task of slice 5b: a NULL alias stays
NULL instead of the next rowid; a non-integer alias is stored instead of the mismatch
error; the rowid ignores an explicit alias; UPDATE of the alias keeps the old rowid; a
table constraint `PRIMARY KEY(id)` makes no alias."""

TARGETS: dict[str, tuple[str, ...]] = {
    "null_alias_stays_null": ("alias-null",), "non_integer_alias_stored": ("alias-mismatch-hex",),
    "alias_value_not_rowid": ("alias-negative",), "update_keeps_rowid": ("alias-update-move",),
    "table_constraint_not_alias": ("alias-table-constraint",),
}
"""The authored case of `conformance.authored_aliases` that each mutant changes."""

GUARDS: dict[str, str] = {
    "null_alias_stays_null": "rule:newCells", "non_integer_alias_stored": "rule:aliasMismatch",
    "alias_value_not_rowid": "rule:newRowid", "update_keeps_rowid": "rule:movedRowid",
    "table_constraint_not_alias": "rule:addTableConstraints",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
