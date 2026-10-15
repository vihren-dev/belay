# Status: rowid aliases (slice 5b)

Created 2026-10-15. Status: IN PROGRESS.
Task: [task](20261015-rowid-aliases.task.md).
Specification: [ADR 0012, Amendment 4, "Rowid aliases (slice 5b)"](../docs/adr-0012-query-semantics.md).

Relevant files: `packages/belay-sqlite/Belay/Sqlite/Model.lean`, `Declarations.lean`,
`Execution.lean`, `LiteralData.lean`, `RowUpdate.lean`, `SqlExecution.lean`,
`LiteralPreservation.lean`, `WritePreservation.lean`, `Resolution/Definitions.lean`,
`Resolution/Writes.lean`, `Resolution/Updates.lean`, `Resolution/Restrictions.lean`,
`packages/verifier-conformance/VerifierConformance/Case.lean`, `docs/semantic-subset.md`.

## Progress

- 2026-10-15: task and status files created. Native 3.51.0 checked: alias values on
  INSERT (NULL, omitted, `NOT NULL`, `' 7 '`, `'8.0'`, negative, the largest rowid, and the
  mismatches `'0x10'`, `1.5`, `1e20` and a BLOB), UPDATE of the alias (NULL and text are
  mismatches, a duplicate is a unique failure), the declaration forms (`integer primary
  key`, table constraint, `DESC`, `INT`), and the random rowid after the largest one.
- 2026-10-15: native check of the error order: rows are inserted in order, and a row's
  alias mismatch comes before its constraints, so `('x'), (1)` is a mismatch and
  `(1), ('x')` a unique failure (1 a duplicate); UPDATE assigns a constant, so every
  selected row or none mismatches.
- 2026-10-15: the model: `Row.Aliased` and `Table.RowsValid` in `Table.Valid`;
  `LiteralData.newRowid`, `newCells` and `aliasMismatch` for INSERT, `movedRowid` and
  `updateMismatch` for UPDATE, `insertOutcome` for the error order, and the new
  `ExecutionError.datatypeMismatch` (code 20, step). `checkedWrite` also requires distinct
  rowids (`rowidsDistinct`), so the preservation proofs (`AliasPreservation.lean`,
  `WritePreservation.lean`) take distinct rowids from the check instead of from fresh
  rowids. New admission conjuncts `aliasReady` (INSERT and UPDATE) and the bounded rowids
  of UPDATE, each with a reason in `conformance/obligation_mutants.py`. `rowid-alias`
  leaves the registry; `CatalogTable.supported` admits aliases. In
  `verifier-conformance`, `RETURNING` of INSERT reads the inserted rows (the rowid of a
  NULL alias), and a mismatch has the output of a failed write. Lean examples in
  `AliasExamples.lean`.
- 2026-10-15: 24 authored cases (`conformance/authored_aliases.py`, all AGREE), five
  mutants (`conformance/alias_mutants.py`, in the write and join measurement), and the
  corpus 18 writer.
- 2026-10-15: callers outside the model follow `Table.Valid`: the Atuin example witness
  (`examples/atuin/AtuinWitness.lean`), the schema examples and the demonstration of the
  verifier package, and the shape test; the write and row-write mutants that named the
  changed INSERT output and `checkedWrite` follow the new text.

## Remaining

- Full checks, CI time, PR A; then PR B (claim corpus 18, `mustAgree`).
