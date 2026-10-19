# Status: CHECK and named constraints (ADR 0014, slice 4)

Created 2026-10-19. Status: open.
Task file: [task](20261019-check-constraints.task.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D2.

## Relevant files

- Syntax and frontend: `Resolution/Syntax.lean`, `Resolution/SyntaxExpr.lean`,
  `belay/sqlite/syntax_definitions.py`.
- Catalog and resolution: `Resolution/Catalog.lean`, `Resolution/Definitions.lean`.
- Execution: `LiteralData.lean`, `Execution.lean`, `RowUpdate.lean`, `Upsert.lean`,
  `UpsertRun.lean`, `Resolution/ConflictPolicy.lean`.

## Progress

- 2026-10-19: native behaviour checked with 3.51.0: CHECK constraints run in written order
  after NOT NULL and before the unique keys; the label is the name, else the trimmed text,
  dequoted when it starts with a quote; NULL passes; `OR IGNORE` skips, `OR REPLACE` aborts,
  `OR FAIL` keeps the earlier rows; `random()` and `CURRENT_TIMESTAMP` are admitted by
  SQLite, `date('now')` is a step error, a JSON failure is `malformed JSON`; ADD COLUMN
  with CHECK over existing rows fails with `CHECK constraint failed` and keeps the
  catalog; `CHECK ... ON CONFLICT` is a syntax error; `PRAGMA foreign_keys` is 0; the
  three foreign-key prepare errors; a missing referenced table is admitted.

## Remaining

- All outcomes, checks, reviews, CI time, pull requests.
