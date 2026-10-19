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

- 2026-10-19: outcomes 1 to 8 in one commit. Syntax `check` (with the label that the
  frontend computes from the name in effect or the trimmed text), `references` and
  `foreignKey`; `CheckConstraint` on columns and tables (`Resolution/Checks.lean`),
  resolved last by `Resolution/TableChecks.lean`; the three foreign-key prepare errors;
  `constraints` and `upsertRow` check CHECK after NOT NULL and before the keys, with the
  statement's algorithm (`ConflictPolicy.check`); ADD COLUMN checks the rows with the new
  default (`ExecutionError.checkColumnDefault`, code 1) and its `quick_check` output name.
  The restriction `create-table-constraints` and `CatalogTable.plain` are gone; new
  restrictions `check-function` and `add-column-check-error`. The frontend helpers moved to
  `syntax_shapes.py`, and `AddColumn.lean` and `ReservedNames.lean` split two files over
  200 lines. Authored corpus `authored_checks` (31 cases, all AGREE with kernel proofs
  locally, corpus 32) and `check_mutants` (four).

- 2026-10-19: the first verdict found a spec error: ADR 0014 D2 said the catalog keeps no
  foreign key, but the judge compares `PRAGMA foreign_key_list`, so 18 agreeing cases
  disagreed. The owner chose to keep foreign keys as inert metadata (owner decision 4,
  recorded in the ADR). The catalog keeps them with their actions on columns and tables
  (`Resolution/ForeignKeys.lean`), the prediction renders the rows, and a record without a
  profile and with a foreign key is out of scope (its setup may turn foreign keys on). The
  atuin and constant-default examples and the core module count follow. Verdict: 201
  upstream cases newly agree (v1 +13, v2 +13, v3 +16, v4 +58, v5 +99, v6 +2), none leaves
  AGREE. The authored corpus has 32 cases.

- 2026-10-19: checks. Fixes after the suite runs: the examples and tests that named the
  removed `CatalogTable.plain` or expected a CREATE TABLE with constraints to stay
  restricted; the harness compares a primary key without repeated columns, as
  `table_xinfo` gives each column once, and a `WITHOUT ROWID` key drops repeats as SQLite
  does; the authored catalog has `check-abort` agree. `just test-full`, `just test-nix`
  and `just test-scheduled` pass. Verdict: 201 upstream cases newly agree (v1 +13, v2 +13,
  v3 +16, v4 +58, v5 +99, v6 +2; v5: 1,210 → 1,309), none leaves AGREE; corpus 32 (32
  cases) agrees in full with kernel proofs.

- 2026-10-19: CI time (local, forced rebuilds), slice 3 → slice 4: harness 21 → 22 s,
  model 364 → 385 s, frozen 140 → 141 s, mutants 519 → 551 s (four new mutants). PR B:
  corpus 32 recorded natively (32 cases) and claimed in full; the 201 upstream cases join
  `mustAgree`; new judge lock.

## Remaining

- Pull requests A and B.
