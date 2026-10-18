# Status: invariants in types, API lemmas and position-free effects (ADR 0013, step 7)

Created 2026-10-18. Status: open.
Task file: [task](20261018-types-and-api.task.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), D8 and D7.

## Relevant files

- Errors: `packages/belay-sqlite/Belay/Sqlite/Resolution/Resolved.lean` (`PrepareError`),
  `Values.lean` (`ValueIssue`), `ErrorKinds.lean`, `IssueLemmas.lean`, `OperandIssues.lean`,
  `ReturningIssues.lean`, `InsertCellRules.lean`, `UpdateRules.lean`, `UpsertRules.lean`,
  `PrepareRules.lean`, `DefinitionRules.lean`, `PrepareSpec.lean`, `Messages.lean`,
  `Codec/Resolution.lean`, `SchemaScript.lean`.
- Reals: `Arithmetic.lean` (`realValue`, `isNullCell`), `Comparison.lean` (`isNull`),
  `StoreValue.lean`, `Json/SqlValue.lean`, `Model.lean` (`Table.Valid`).
- Effects: `StatementStep.lean`, `Execution.lean`, `UpsertRun.lean`, `Laws.lean`,
  `StepCatalog.lean`, `SqlProofs.lean`.
- Users of unfolding: `packages/sqlite-verifier/SqliteVerifier/*Demonstration.lean`,
  `examples/*/Proofs.lean`, `examples/atuin/AtuinFacts.lean`.

## Progress

- 2026-10-18: code map (see the task file's key points). 36 `PrepareError` constructors,
  5 of which name a catalog object; only `noSuchTable` of a `FROM` table reaches
  `ValueIssue` among those. The `_issue` lemma family has no users outside
  `Resolution/`.
- 2026-10-18: `Resolved.Statement.kind` (outcome 7, in `StatementCatalog.lean`):
  `isControl`, `SchemaOnly` and `NoWrites` classify through it, and `nonControl` is gone.
  `prepareError?` stays a match because it returns the error.
- 2026-10-18: owner decision 8 (ADR 0013): every computed REAL is built through
  `realValue` (literals, the most negative integer default, JSON payloads) or keeps the
  bits of a REAL (`integerAffinity`, `realRead`, documented); `Value.isNull` (in
  `Declarations.lean`) replaces `isNull` by rank and `isNullCell`; `Table.Valid` does not
  change, because `Float` is opaque to proofs. The task's outcome 2 is amended by the
  decision. Verdict counts unchanged (the step 5 reports were collected by the GC;
  `build/agent-logs/report-s7b.json` keeps this one for later diffs).
- 2026-10-18: `PrepareError` keeps the five errors that name a catalog object and
  `expression (ExprError)`; `ExprError` has the 31 others, and `ValueIssue.prepare` carries
  an `ExprError`. A missing `FROM` table is `SourceIssue.noSuchTable`, outside
  `ValueIssue`. The definition helpers (`keyPositions`, `mergeAlgorithm`, `addUniqueKey`,
  `setPrimaryKey`, `addDefinitions`, `addTableConstraints`, `insertPositions`) return
  `ExprError`. `ErrorKinds`, `IssueLemmas`, `OperandIssues`, `ReturningIssues`,
  `InsertCellRules`, `UpsertRules` and `PrepareSpec` are gone, and the prepare rules take
  "the error is not `.expression`" as their premise. `ToJson PrepareError` keeps the
  derived wire form (examples in `Codec/SourceExamples.lean`); messages are unchanged.
  The core has 127 modules. Verdict unchanged, entry for entry.
- 2026-10-18: proof files of `belay-sqlite` end in `Laws`, `Spec` or `Examples`
  (`PreservationLaws`, `DatabaseLaws`, `ModelLaws`, `SqlLaws`, `LiteralPreservationLaws`,
  `SchemaExtensionLaws`, `SchemaPreservationLaws`, `StepCatalogLaws`, `ModelProjectionLaws`,
  `SchemaClockLaws`, `DatabaseWriteLaws`, `CatalogAgreementLaws`; `PrepareSpec`,
  `DefinitionSpec`, `UpdateSpec`, `WriteCatalogSpec`), and the package has a README.
  `step` and `literalStep` return a position-free `Effect`; `SqlState.publish` is the one
  publication path (FAIL keeps the reached rows, other errors the state's database,
  ROLLBACK the snapshot), and `LiteralData.failedDatabase` is gone. `ScriptLaws.lean` has
  `runSql_eq`, `runSqlFrom_nil`, `runSqlFrom_cons`, `advance_effect` (and an unconditional
  `advance_*` lemma for each ordinary form, because `simp` cannot assign the proof of the
  side condition), `SqlState.publish_ok`, `publish_error_idle`, `publish_prepare_idle`,
  `effect_createTable_ok`, `effect_addColumn_ok`, `effect_write_ok` and
  `effect_prepareError`; the frame lemma is `Database.table_setRows_other`.
  `VerificationConditions.ofSchemaProjection` (`SqliteVerifier/SchemaProjection.lean`)
  gives the conditions of a schema-only script that keeps one projection; the
  demonstrations and `examples/` use these lemmas and no longer unfold the execution.
  The failure mutants now change `SqlState.publish` (`abort_keeps_rows` replaces
  `failed_update_keeps_rows`). The core has 129 modules. Verdict unchanged.
- 2026-10-18: readiness returns results (outcome 6). `runStatement` computes each write and
  query once and gives a `StatementRun` with its effect and its support check;
  `literalStep` and `statementReady` read its fields, and `supportedSqlFrom` and the
  harness's `passFrom` use one run for both (`advanceWith`). `insertReady` and
  `updateReady` take the table that the write computed; the INSERT with clauses runs as a
  trace of reached rows (`upsertSteps`), of which `upsertRun` is the summary and
  `upsertBounded` the rowid check; a query's effect is `queryEffect` of its run
  (`Query.runOn`). The harness's `statementOutput` still recomputes the written rows for
  its outputs. Verdict unchanged.

## Remaining

- Full checks, CI time, pull request.
