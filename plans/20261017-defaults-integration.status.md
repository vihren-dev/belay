# Literal defaults in the ADR 0012 stack, slice 6e1 of ADR 0012: status

Created 2026-10-17. Status: open.
Task: [20261017-defaults-integration.task.md](20261017-defaults-integration.task.md).
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), Amendment 5, owner
decisions 8 and 9.

## Relevant files

- #130: `tasks/constant-column-defaults` (head `ae14a73b02c3`), its task and status files.
- Conflicts of a trial merge: `docs/semantic-subset.md`, `Codec/Resolution.lean`,
  `Execution.lean`, `Resolution/Catalog.lean`, `Resolution/Context.lean`,
  `Resolution/Definitions.lean`, `Resolution/Syntax.lean`, `Resolution/Writes.lean`,
  `SchemaExtension.lean`, `SqlExecution.lean`, `VerifierConformance/Case.lean`,
  `Outputs.lean`, `Predict.lean`, `tests/conformance_pipeline_test.py`,
  `tests/syntax_mapping_test.py`, `tests/test_model_package.py`.

## Progress

- 2026-10-17: owner decisions 8 (clock domain and relation) and 9 (build on #130)
  recorded in ADR 0012; task and status files, stacked on #149.

## Remaining

- Merge, conflicts, interactions, full checks, review, CI time, pull request A; then
  pull request B if cases newly agree. Then slice 6e2 (the clock).
