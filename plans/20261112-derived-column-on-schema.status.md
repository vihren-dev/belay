# Status: short proofs of the derived-column migration on a schema

Created 2026-11-12. Task: `20261112-derived-column-on-schema.task.md`. Issue #376.
Status: specification complete; implementation pending.

## References

- Laws: `packages/belay/Belay/Sqlite/Programs/StatementRunLaws/DerivedColumnMigration.lean`,
  `DerivedColumnQueries.lean`, `DerivedColumnReads.lean`.
- Site and reads: `packages/belay/Belay/Sqlite/Schema/Columns/DerivedColumnMigration.lean`,
  `DerivedColumnReads.lean`.
- Model steps: `addColumn_plain_step`, `backfill_step`, `derivedColumn_state` in
  `packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/StatementRunLaws/`.
- Hand proof to replace: `tests/surface/Schema/Tests/DerivedColumnSchemaPremise.lean`.
- Page for agents: `docs/guide/agents.md`.

## Progress

- 2026-11-12: task and status files.

## Tests of each commit

- None yet.
