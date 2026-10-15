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

## Remaining

- Everything in the task's "Outcome".
