# Status: `WITHOUT ROWID` tables (ADR 0014, slice 2)

Created 2026-10-19. Status: open.
Task file: [task](20261019-without-rowid.task.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D4.

## Relevant files

- Frontend and Syntax: `belay/sqlite/syntax_definitions.py`, `Resolution/Syntax.lean`.
- Catalog and resolution: `Resolution/Catalog.lean`, `Resolution/Definitions.lean`,
  `Resolution/Scope.lean`, `Resolution/QueryExprs.lean`.
- Execution: `QueryEval.lean` (source rows).
- Harness: `packages/verifier-conformance/VerifierConformance/Native.lean`, `Predict.lean`,
  `Json.lean`, `conformance/native_replay.py`, `conformance/predict_render.py`.

## Progress

- 2026-10-19: native behaviour checked with 3.51.0: `PRIMARY KEY missing on table n`; key
  columns report NOT NULL in `table_xinfo`; `INTEGER PRIMARY KEY` is no alias and refuses
  NULL; `rowid` is `no such column`; a scan is in key order, descending for
  `PRIMARY KEY DESC`; the table has a `pk` index.

- 2026-10-19: outcomes 1 to 4 in one commit. Syntax `createTable` has `TableOptions`
  (`withoutRowid`), mapped from the table option set; STRICT stays refused; record
  version 5 (the frozen model cases and the regression record get `options`, and the
  regression hash). `CatalogTable.withoutRowid` and `asWithoutRowid` (key columns NOT NULL,
  no alias); `primaryKeyMissing`; `ScopeSource.hasRowid` makes rowid names `no such column`
  over such tables; `Table.scanRows` orders a scan by rowid or by key, used by queries and
  by the harness's UPDATE and DELETE outputs. The harness has `NativeTable.withoutRowid`
  (written only when true) and compares such rows by cells in key order; the prediction
  renders the key cells as identity. Authored corpus `authored_without_rowid` (17 cases,
  corpus 30) and `without_rowid_mutants` (two). ADR 0014 records the hidden-rowid design.

## Remaining

- Suites, verdict, review, CI time, pull requests A and B.
