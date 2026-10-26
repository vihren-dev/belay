"""Mutants of generated columns (ADR 0014, slice 5).

The task of slice 5 lists the changes that the conformance suite must notice. Each mutant
is one text change in a copy of the model, which `conformance.resolve_mutants.measure`
builds and runs against its target case of `conformance.authored_generated`.
"""

from conformance.resolve_mutants import SQLITE

ROW_UPDATE = SQLITE + "RowUpdate.lean"
"""The new row of an UPDATE."""
NATIVE = "verifier-conformance/VerifierConformance/Native.lean"
"""The `hidden` value that the harness compares with `PRAGMA table_xinfo`."""
WRITES = SQLITE + "Resolution/Writes.lean"
"""The column list of an INSERT."""

MUTANTS: dict[str, tuple[str, str, str]] = {
    "generated_not_recomputed": (ROW_UPDATE,
        "  { row with values := generatedCells columns (assignments.foldl (fun values (position, expression) =>\n"
        "      values.set position (Value.store (positionAffinity columns position) (expression.eval context cells))) "
        "row.values) }",
        "  { row with values := assignments.foldl (fun values (position, expression) =>\n"
        "      values.set position (Value.store (positionAffinity columns position) (expression.eval context cells))) "
        "row.values }"),
    "stored_hidden_virtual": (NATIVE, "  | some { stored := true, .. } => 3", "  | some { stored := true, .. } => 2"),
    "insert_fills_generated": (WRITES, "  | none => pure (writablePositions columns)",
        "  | none => pure (List.range columns.length)"),
}
"""Each mutant: the file under `packages/`, the exact text it changes, and the replacement.
The names follow the list in the task of slice 5: a generated value that UPDATE does not
recompute, the `hidden` value of a VIRTUAL column for a STORED one, and an INSERT without a
column list that expects a value for each generated column."""

TARGETS: dict[str, tuple[str, ...]] = {
    "generated_not_recomputed": ("generated-update",),
    "stored_hidden_virtual": ("generated-values",),
    "insert_fills_generated": ("generated-insert-without-columns",),
}
"""The authored case of `conformance.authored_generated` that each mutant changes."""

GUARDS: dict[str, str] = {
    "generated_not_recomputed": "rule:assignFrom",
    "stored_hidden_virtual": "rule:columnHidden",
    "insert_fills_generated": "rule:insertPositionsTraced",
}
"""What each mutant guards: `rule:` and the Lean declaration of its file that the mutant
changes. `conformance.mutant_guards` checks every entry."""
