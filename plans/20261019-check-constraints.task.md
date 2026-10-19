# CHECK and named constraints, and CREATE TABLE with constraints in the script (ADR 0014, slice 4)

Created 2026-10-19. Status: open.
Status file: [status](20261019-check-constraints.status.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D2 and owner decision 3; the
[measurement](../experiments/schema-features/README.md).

## Pull requests

- **A (subject):** the model, the frontend, the harness and an authored corpus, stacked on
  slice 3 (#181). Nothing under `judge/` changes.
- **B (claims), only if cases newly agree.**

## Outcome

1. **Syntax.** A column constraint `CHECK (expr)` and a table constraint `CHECK (expr)` map
   to the Syntax IR with the source text between the parentheses. `CONSTRAINT name` may
   come before any column or table constraint. `REFERENCES table [(column)]` with its
   clauses (`ON DELETE`, `ON UPDATE`, `MATCH`, `DEFERRABLE`) and the table constraint
   `FOREIGN KEY (columns) REFERENCES table [(columns)]` map too.
2. **The catalog.** A table has its CHECK constraints in written order (column constraints
   and table constraints as they appear), each a resolved condition over the row and the
   label that SQLite reports: the constraint's name, else the source text between the
   parentheses without leading and trailing white space, dequoted when it starts with a
   quote (`CHECK ("a" > 0)` reports `a`). A name before any other constraint has no
   effect. The catalog keeps the foreign keys (outcome 4).
3. **Resolution of a CHECK** follows SQLite's prepare errors, checked natively with 3.51.0:
   `subqueries prohibited in CHECK constraints`, `no such column`, `misuse of aggregate
   function`, and the profile's `DQS_DDL` for a double-quoted name. A qualified name of the
   table and `rowid` are allowed.
4. **Inert foreign keys** (owner decision 3). Every profile the model has runs with foreign
   keys off (SQLite's default, `PRAGMA foreign_keys` is 0), so a `REFERENCES` clause or a
   `FOREIGN KEY` constraint has no effect apart from SQLite's prepare errors:
   `unknown column "c" in foreign key definition`, `number of columns in foreign key does
   not match the number of columns in the referenced table`, and `foreign key on c should
   reference only one column of table t`. The referenced table need not exist. The catalog
   keeps each foreign key as inert metadata, which the prediction reports as
   `PRAGMA foreign_key_list` does (owner decision of 2026-10-19: the judge compares those
   rows). A record without an execution profile and with a foreign key stays out of scope,
   as its setup may have turned foreign keys on.
5. **Execution.** INSERT, UPDATE and the `DO UPDATE` of an UPSERT check the CHECK
   constraints of each written row in SQLite's order: NOT NULL, then CHECK in written
   order, then the unique keys. A CHECK fails when its condition is false; NULL passes.
   A failure is SQLite's constraint error (`CHECK constraint failed: label`). `OR IGNORE`
   skips the row, `REPLACE` acts as `ABORT`, and `FAIL`, `ROLLBACK` and `ABORT` keep their
   meaning.
6. **ADD COLUMN with CHECK.** On a table with rows, SQLite checks the new column's CHECK
   over the existing rows and fails with `CHECK constraint failed` (no label), leaving the
   catalog as it was; on an empty table it succeeds. Natively this is result code 1
   (`SQLITE_ERROR`) at step, not a constraint error; a failing CHECK of a write is 275
   (`SQLITE_CONSTRAINT_CHECK`).
7. **CREATE TABLE in the script.** A CREATE TABLE with constraints or defaults that runs in
   the script uses the catalog function of a described one, and the restriction
   `create-table-constraints` goes.
8. **Restrictions.** A CHECK that reads a value SQLite may compute differently on each
   evaluation (`random()`, a time keyword, a date and time function), or whose evaluation
   can fail (a JSON function), is a model restriction. `date('now')` in a CHECK is a step
   error natively, so the model does not describe it either.

## Tests

- Lean examples: each rule of outcomes 2 to 6; the label forms; the order NOT NULL, CHECK,
  unique keys; NULL passing; each conflict algorithm; ADD COLUMN on an empty and a
  populated table; a CREATE TABLE with keys and defaults that runs; each prepare error.
- An authored corpus (`conformance/authored_checks.py`) of these cases, each with a kernel
  proof, recorded as a new corpus.
- The verdict of every corpus: cases that newly agree and none that leave AGREE.
- Mutants: a CHECK that NULL fails, CHECK after the unique keys, `REPLACE` that replaces for
  a CHECK, and an UPDATE that skips the CHECK, each killed by an authored case.

## Key points

- **Files.** `Resolution/Syntax.lean` and `Resolution/SyntaxExpr.lean` (constraints),
  `Resolution/Catalog.lean` (`CatalogTable`), `Resolution/Definitions.lean` (the catalog
  function and the restriction `create-table-constraints`), `LiteralData.lean`
  (`constraints`, `tableReady`, `insertReady`), `Execution.lean` (INSERT, ADD COLUMN),
  `RowUpdate.lean`, `Upsert.lean` and `UpsertRun.lean` (the write paths and their NOT NULL
  checks), `Resolution/ConflictPolicy.lean` (algorithms),
  `belay/sqlite/syntax_definitions.py`, and the harness (`predict_render.py` renders the
  catalog; SQLite's `PRAGMA` inventories do not show CHECK constraints, so the judge sees
  them only through the results of writes).
- **Proofs.** `tableReady` and the write-preservation laws (`SchemaPreservationLaws.lean`,
  `LiteralPreservationLaws.lean`, `DatabaseWriteLaws.lean`) state what a stored table
  satisfies. The CHECK constraints join that invariant, or the laws say why they need not.
- **Kernel cost.** A table without CHECK constraints must cost no more kernel time. Keep
  the checks of such a table as cheap as today, and keep every new function reducible by
  the kernel (no well-founded recursion; slice 3 found one that got stuck).
- **UPDATE.** SQLite checks only the CHECK constraints that read an updated column. Every
  stored row satisfies every CHECK, and the deterministic CHECKs that the model admits
  give the same value on the same row, so checking all of them gives the same result.
- **Record version.** New Syntax fields change the structural record's version, as slice 2
  did; a new constructor alone does not.
