# Status: execution carries the catalog (ADR 0013, step 2)

Created 2026-10-18. Status: open.
Task file: [task](20261018-execution-carries-catalog.task.md).
Specification: [ADR 0013](../docs/adr-0013-model-structure.md), D1 and amendment 1.

## Relevant files

- Model: `packages/belay-sqlite/Belay/Sqlite/Model.lean`, `Execution.lean`,
  `StatementStep.lean`, `LiteralData.lean`, `RowUpdate.lean`, `Upsert.lean`,
  `UpsertRun.lean`, `StatementClock.lean`, `ModelFacts.lean`, `SchemaExtension.lean`,
  `Resolution/Resolved.lean`, `Resolution/Writes.lean`, `Resolution/Updates.lean`,
  `Resolution/Definitions.lean`, `Resolution/Catalog.lean`.
- Preservation chain to delete: `AliasPreservation`, `UpdatePreservation`,
  `WritePreservation`, `UpsertPreservation`, `UpsertConforms`, `DeletePreservation`.
- Conformance: `packages/verifier-conformance/VerifierConformance/Case.lean`,
  `Predict.lean`, `Native.lean`, `Outputs.lean`, `Trace.lean`.
- Contract and gate: `packages/sqlite-verifier/SqliteVerifier/Contract.lean`,
  `ContractProofs.lean`, `Library.lean`, `GateCore.lean`, `GateInputs.lean`,
  `packages/verifier-gate/BundleChecker.lean`, `migration_check/compile.py`.
- Examples: `examples/*`, `packages/sqlite-verifier/SqliteVerifier/*Demonstration.lean`,
  `tests/kernel_gate/`.
- Mutation: `conformance/mutation_check.py`, `conformance/*_mutants.py`,
  `conformance/instrument_model.py`.

## Progress

- 2026-10-18: code map done. The owner chose the full D1 (owner decision 5). ADR 0013
  amendment 1 records the contract change, the approved files, the shared catalog
  functions, the policy split and the verdict risk.
- 2026-10-18: the unused preservation chain is deleted (645 lines; `AlgorithmExamples`
  reads the final table itself). The three suites pass on that commit.
- 2026-10-18: `Catalog.createTable`, `Catalog.createIndex` and `Catalog.addColumn` are the
  catalog changes; the resolver calls them.
- 2026-10-18: the step itself. `Database` is `{ catalog, rows }` with `Database.table` as
  the view, `Database.setRows` and `Database.addColumn`; `DatabaseFacts.lean` states how
  they change the view. Writes read their keys and policy from the state
  (`Database.keys`, `Catalog.writePolicy` in the new `Resolution/ConflictPolicy.lean`);
  UPSERT keeps its `OR` algorithm. Conformance observes databases; `resolveStates`,
  `stateBound`, `observationState` and `Tables` are gone. The contract changes as
  amendment 1 says. `Conforms.replaceRows`, `Conforms.set`, `Database.set_comm` and
  `Catalog.appendAt` are replaced by `Conforms.setRows`, `Database.setRows_comm`,
  `Conforms.addColumn` and `Conforms.createTable`. Only one approved file changes
  (`examples/atuin/approved/HistoryMapping.lean`, `database.table position`); the
  other approved files compile unchanged. `violates_required_catalog` takes its
  catalog premise for admitted databases. The mutant anchors moved.
  `just conformance-coverage` (`conformance/instrument_model.py`) was already stale
  before this step (`c.names`); it is not part of any suite and is not changed here.
- 2026-10-18: `runSqlAt_catalog` (outcome 2): resolution and execution give the same
  catalog for every run without an error, with a checked use in
  `CatalogAgreementExamples.lean`.

- 2026-10-18: the suites found three generated or test sources on the old API
  (`conformance/model_assertions.py`, the observation test, the refutation example)
  and a resolve mutant that no case noticed any more: execution now gives the observed
  catalog, so a wrong resolver catalog after ROLLBACK shows only in a later statement.
  The authored case `rollback_then_add` (recorded natively, frozen in
  `conformance/cases/`) notices it. Reviews: two rounds of proof-sketch, wording and
  file-size findings, fixed in a `refactor:` commit whose review is clean.
- 2026-10-18: the three suites pass. The verdict counts and the report equal step 1's,
  so no pull request B is needed. CI time against step 1: `tests.harness` 22 s to
  22 s, `tests.model` 335 s to 335 s, `tests.frozen` 142 s to 140 s, scheduled mutants
  404 s to 411 s.

## Remaining

- Pull request A.
