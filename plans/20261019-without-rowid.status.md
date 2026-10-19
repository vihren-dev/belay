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

## Remaining

- All outcomes, checks, reviews, CI time, pull requests.
