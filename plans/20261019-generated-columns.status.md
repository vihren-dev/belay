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

- 2026-10-19: outcomes 1 to 6 in one commit. Syntax `generated` (the frontend strips a
  trailing `GENERATED ALWAYS` from the type, as SQLite does); `GeneratedColumn` on catalog
  columns, resolved after the CHECK constraints over the table without the rowid
  (`Resolution/GeneratedColumns.lean`), with the definition errors; `generatedCells`
  computes the values in passes in `newCells` and `assignFrom`; INSERT without a column
  list fills the columns that are not generated; the harness carries `hidden`. New
  restrictions `generated-function`, `generated-loop`, `upsert-generated` and
  `add-column-generated` (the task records the last three as amendments). Authored corpus
  `authored_generated` (21 cases, all AGREE with kernel proofs locally, corpus 33) and
  `generated_mutants` (three).

## Remaining

- Checks, reviews, verdict, CI time, PR B, pull requests.
