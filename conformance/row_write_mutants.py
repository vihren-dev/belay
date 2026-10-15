"""Mutants of row-dependent writes (ADR 0012, amendment 1, "Testing").

The amendment lists the changes that the conformance suite must notice. Each mutant is
one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_row_writes`.
"""

from conformance.resolve_mutants import SQLITE

ROW_UPDATE = SQLITE + "RowUpdate.lean"
"""The execution of UPDATE."""
STORE = SQLITE + "StoreValue.lean"
"""Store-time affinity."""
WRITES = SQLITE + "Resolution/Writes.lean"
"""The resolution of INSERT, which stores each value."""
UPDATES = SQLITE + "Resolution/Updates.lean"
"""The resolution of UPDATE, which stores each constant value."""
EXECUTION = SQLITE + "SqlExecution.lean"
"""The checked write of INSERT and UPDATE."""
OUTPUTS = "verifier-conformance/VerifierConformance/Outputs.lean"
"""The outputs of statements, with the change count."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "set_reads_new_row": (ROW_UPDATE,
        "values.set position (storeValue (positionAffinity columns position) (expression.eval row.values))) row.values }",
        "values.set position (storeValue (positionAffinity columns position) (expression.eval values))) row.values }"),
    "null_filter_selects": (ROW_UPDATE,
        "  filter.all fun condition => Resolved.truthy (condition.eval row.values)",
        "  filter.all fun condition => !Resolved.falsy (condition.eval row.values)"),
    "no_store_affinity": (ROW_UPDATE,
        "values.set position (storeValue (positionAffinity columns position) (expression.eval row.values))) row.values }",
        "values.set position (expression.eval row.values)) row.values }"),
    "no_store_of_constants": (UPDATES,
        "  else .literal (storeValue (columnAffinity scope.columns position) (resolved.eval []))",
        "  else .literal (resolved.eval [])"),
    "cast_as_store_affinity": (WRITES,
        "    .ok (storeValue column.affinity value)) columns", "    .ok (castValue column.affinity value)) columns"),
    "real_column_keeps_integer": (STORE,
        "  | .integer whole => .real (positiveZero (Float.ofInt whole).toBits)", "  | .integer whole => .integer whole"),
    "text_column_keeps_number": (STORE,
        "  | .text, .integer _ | .text, .real _ => .text value.textBytes", "  | .text, .integer _ | .text, .real _ => value"),
    "failed_update_keeps_rows": (EXECUTION,
        "  else .failure position .constraintViolation database",
        "  else .failure position .constraintViolation (database.set at_ result)"),
    "change_count_every_row": (OUTPUTS, "        some chosen.length⟩", "        some table.rows.length⟩"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the
replacement. The names follow the list of the amendment: SET values read the new row; a
NULL filter selects the row; no store affinity (at execution and for constants); `castValue`
as store affinity; a REAL column keeps an integer; a TEXT column keeps a number; a failed
UPDATE keeps the rows that it changed; the change count counts every row. The execution
stores every assigned value again, so a constant that resolution does not store differs
only in the key-domain check: `no_store_of_constants` makes the text `'7'` for a key
column a restriction."""

TARGETS: dict[str, tuple[str, ...]] = {
    "set_reads_new_row": ("update-swap",), "null_filter_selects": ("update-null-filter",),
    "no_store_affinity": ("update-stores-row-value",), "no_store_of_constants": ("update-key-number-text",),
    "cast_as_store_affinity": ("store-other-text",), "real_column_keeps_integer": ("store-integer-into-real",),
    "text_column_keeps_number": ("store-whole-real",), "failed_update_keeps_rows": ("update-not-null-failure",),
    "change_count_every_row": ("update-no-match",),
}
"""The authored case of `conformance.authored_row_writes` that each mutant changes."""

GUARDS: dict[str, str] = {
    "set_reads_new_row": "rule:assign", "null_filter_selects": "rule:selected",
    "no_store_affinity": "rule:assign", "no_store_of_constants": "rule:assignedExpression",
    "cast_as_store_affinity": "rule:fullRow", "real_column_keeps_integer": "rule:realRead",
    "text_column_keeps_number": "rule:storeValue", "failed_update_keeps_rows": "rule:checkedWrite",
    "change_count_every_row": "rule:statementOutput",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
