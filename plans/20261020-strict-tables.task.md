# `STRICT` tables (ADR 0014, slice 6)

Created 2026-10-20. Status: DONE (pull requests #189 and #190).
Status file: [status](20261020-strict-tables.status.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D6.

## Pull requests

- **A (subject):** the model, the frontend and an authored corpus, stacked on slice 5
  (#186). Nothing under `judge/` changes.
- **B (claims), only if cases newly agree.**

## Outcome

1. **Syntax.** The table option `STRICT` maps to the Syntax IR, alone and with
   `WITHOUT ROWID`.
2. **Declared types.** In a `STRICT` table every column has one of the types `INT`,
   `INTEGER`, `REAL`, `TEXT`, `BLOB` and `ANY`, with ASCII case ignored; another type is
   SQLite's prepare error `unknown datatype for t.a: "VARCHAR(10)"`, and a column without a
   type `missing datatype for t.a`. `ANY` stores a value as written, with no affinity; the
   other types keep their affinity.
3. **Writes.** After the column's affinity applies, a value whose storage class does not fit
   the type fails the statement: `cannot store TEXT value in INTEGER column s.a`, result
   code 19. NULL fits every type; an `INT` or `INTEGER` column takes integers, `REAL`
   integers and reals (the affinity stores both as reals), `TEXT` text, `BLOB` blobs, and
   `ANY` every value. Checked natively with 3.51.0:
   - the check comes after NOT NULL and before CHECK and the unique keys, and also covers
     generated columns and `DO UPDATE`;
   - the type check is ABORT under every algorithm: `OR FAIL` keeps no earlier row,
     `OR ROLLBACK` keeps the transaction open, and `OR IGNORE` and `OR REPLACE` fail
     (`OP_TypeCheck` ends with `abort_due_to_error`; amended 2026-10-20 after a native
     check, which an earlier probe got wrong);
   - a rowid alias keeps its own rule (`datatype mismatch`).
4. **ADD COLUMN** to a `STRICT` table with a type that is not allowed fails while the
   statement runs (`error in table r after add column: unknown datatype ...`), which the
   model leaves as a restriction. So does a default that does not fit the type, which
   SQLite reports as `type mismatch on DEFAULT` while the statement runs, when the table
   has rows. Each primary-key column other than the rowid alias is NOT NULL, with ABORT
   unless it declares its own (`sqlite3EndTable`). A column's affinity and its default follow its strict type (an `ANY` default
   `'7'` stays text), and ADD COLUMN to a `STRICT` table has the output column of SQLite's
   SELECT over `pragma_quick_check`.

## Tests

- Lean examples: each rule of outcomes 2 and 3; each type with a value that fits and one
  that does not; the order NOT NULL, type, CHECK; each conflict algorithm; `ANY` without
  affinity; `STRICT, WITHOUT ROWID`.
- An authored corpus (`conformance/authored_strict.py`) of these cases, each with a kernel
  proof, recorded as a new corpus.
- The verdict of every corpus: cases that newly agree and none that leave AGREE.
- Mutants: a type check that NULL fails, `ANY` with affinity, and IGNORE that skips a
  type error, each killed by an authored case.

## Key points

- **Files.** `Resolution/Syntax.lean` (`TableOptions`), `Resolution/Catalog.lean`
  (`CatalogTable`), `Resolution/Definitions.lean` and `Resolution/AddColumn.lean`,
  `Resolution/TypeAffinity.lean` (the affinity of `ANY`), `LiteralData.lean` and
  `UpsertRun.lean` (the write checks), `Resolution/ConflictPolicy.lean` (the algorithm),
  `belay/sqlite/syntax_definitions.py` (`table_options` refuses `STRICT` today).
- **Record version.** The new field of `TableOptions` changes the structural record's
  version, as slice 2 did, unless its decoder reads a missing field as false.
- **Kernel cost.** A table that is not `STRICT` must cost no more kernel time.
