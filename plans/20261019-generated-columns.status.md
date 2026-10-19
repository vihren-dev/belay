# Status: generated columns (ADR 0014, slice 5)

Created 2026-10-19. Status: open.
Task file: [task](20261019-generated-columns.task.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D5.

## Progress

- 2026-10-19: native behaviour checked with 3.51.0: `table_xinfo` reports `hidden` 2 for
  `VIRTUAL` and 3 for `STORED`; an INSERT without a column list takes values for the
  columns that are not generated; `cannot INSERT into generated column "b"` and `cannot
  UPDATE generated column "c"` are prepare errors; the PRIMARY KEY and DEFAULT errors; a
  loop fails CREATE TABLE at step; ADD COLUMN of a STORED column fails at step; UNIQUE,
  NOT NULL and CHECK apply; `random()` and `rowid` are prepare errors in the expression;
  the recorder reads generated values as row cells.

## Remaining

- All outcomes, checks, reviews, CI time, pull requests.
