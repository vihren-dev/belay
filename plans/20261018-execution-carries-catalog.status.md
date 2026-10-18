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

## Remaining

- Implementation, full checks, verdict measurement, review, CI time, pull request A;
  pull request B if a verdict changes.
