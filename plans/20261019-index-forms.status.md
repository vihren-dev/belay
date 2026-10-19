# Status: index forms (ADR 0014, slice 1)

Created 2026-10-19. Status: open.
Task file: [task](20261019-index-forms.task.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D1.

## Relevant files

- Syntax and frontend: `packages/belay-sqlite/Belay/Sqlite/Resolution/Syntax.lean`,
  `belay/sqlite/syntax_definitions.py`.
- Catalog and keys: `Resolution/Catalog.lean`, `LiteralData.lean`, `Upsert.lean`,
  `RowUpdate.lean`, `Resolution/Upserts.lean`, `Resolution/ConflictPolicy.lean`.
- Resolution and execution: `Resolution/Definitions.lean`, `Execution.lean`,
  `StatementStep.lean`.
- Harness: `packages/verifier-conformance/VerifierConformance/Native.lean`,
  `Predict.lean`, `conformance/native_metadata.py`, `conformance/predict_render.py`.

## Progress

- 2026-10-19: native behaviour of index forms checked with 3.51.0 (prepare errors of
  terms and filters, `date('now')` refused only when a row is written, a string term read
  as a column, partial unique indexes over existing rows). The judge compares partial
  indexes, expression keys and sort orders already, so no judge change.

## Remaining

- All outcomes, checks, reviews, CI time, pull requests.
