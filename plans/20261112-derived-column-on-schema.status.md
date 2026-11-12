# Status: short proofs of the derived-column migration on a schema

Created 2026-11-12. Task: `20261112-derived-column-on-schema.task.md`. Issue #376.
Status: in progress; reads (a) done, success (b) and example (c) pending.

## References

- Laws: `packages/belay/Belay/Sqlite/Programs/StatementRunLaws/DerivedColumnMigration.lean`,
  `DerivedColumnQueries.lean`, `DerivedColumnReads.lean`.
- Site and reads: `packages/belay/Belay/Sqlite/Schema/Columns/DerivedColumnMigration.lean`,
  `DerivedColumnReads.lean`.
- Model steps: `addColumn_plain_step`, `backfill_step`, `derivedColumn_state` in
  `packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/StatementRunLaws/`.
- Computed check (a): `Schema/Columns/DerivedColumnSiteCheck.lean`, `DerivedColumnReadCheck.lean`,
  `Programs/StatementRunLaws/DerivedColumnSchema.lean` (all under `packages/belay/Belay/Sqlite/`); model
  parts `Queries/Evaluation/ExprFormChecks.lean` and `Schema/Dispatch/SelectTableParts.lean` (under
  `packages/belay-sqlite-model/Belay/Sqlite/Model/`).
- Hand proof to replace: `tests/surface/Schema/Tests/DerivedColumnSchemaPremise.lean`.
- Page for agents: `docs/guide/agents.md`.

## Progress

- 2026-11-12: task and status files.
- 2026-11-12: reads (a). `siteCheck` and `Site.ofCheck` give the site from the catalog; `readCheck` and
  `Site.ReadPreserved.ofCheck` give the read facts; `preservesCheck`, `preserves_of_check` and
  `preserves_of_check_forall` give `M preserves Q on schema` from the scripts as `sql` text. Fixture
  `DerivedColumnCheckBoundaries` covers the false cases and a second schema. The check works on a `db!`
  schema and on a run of a script.

## Tests of each commit

- Reads (a): `tests/surface_derived_column_test.py -k boundaries`.
