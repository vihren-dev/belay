# Status: generated columns (ADR 0014, slice 5)

Created 2026-10-19. Status: DONE.
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
  `authored_generated` (23 cases after the first review, all AGREE with kernel proofs locally, corpus 33) and
  `generated_mutants` (three).

- 2026-10-19/20: reviews and checks. Two review rounds with new "must" findings (a
  qualified name and a second `AS`; then the frontend's case folding, a quoted kind, and
  SQLite's textual rule for a trailing `GENERATED ALWAYS` on bytes before dequoting); the
  owner chose to continue after the second round. Lean could not build the stripped type
  String in a way the kernel reduces, so the frontend applies that lexical rule, with an
  explicit ASCII comparison, before it dequotes. `columnHidden` replaces a `_root_`
  declaration that the model mutation tests copy into several namespaces. The disk guard
  needed the owner-approved cleanup of old `/tmp/nix-shell.*` directories. `just
  test-full`, `just test-nix` and `just test-scheduled` pass. Verdict: 66 upstream cases
  newly agree (v4 +33, v5 +33; v5: 1,309 → 1,342), none leaves AGREE; corpus 33 (23 cases)
  agrees in full with kernel proofs.

- 2026-10-20: CI time (local, forced rebuilds), slice 4 → slice 5: harness 22 → 22 s,
  model 385 → 395 s, frozen 141 → 143 s, mutants 551 → 583 s (three new mutants).

## Remaining

- 2026-10-20: PR B (corpus 33, 23 cases, claimed in full; the 66 upstream cases join
  `mustAgree`; new judge lock); pull requests #185 (A) and #186 (B). DONE.
