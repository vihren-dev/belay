# Generated columns (ADR 0014, slice 5)

Created 2026-10-19. Status: open.
Status file: [status](20261019-generated-columns.status.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D5; the
[measurement](../experiments/schema-features/README.md).

## Pull requests

- **A (subject):** the model, the frontend, the harness and an authored corpus, stacked on
  slice 4 (#184). Nothing under `judge/` changes: the judge compares the `hidden` field of
  `PRAGMA table_xinfo` and the rows, which hold the values of generated columns.
- **B (claims), only if cases newly agree.**

## Outcome

1. **Syntax.** A column constraint `[GENERATED ALWAYS] AS (expr) [VIRTUAL | STORED]` maps
   to the Syntax IR; without a keyword the column is `VIRTUAL`.
2. **The catalog.** A column may be generated, with its kind and a resolved expression over
   the row. `PRAGMA table_xinfo` reports a `VIRTUAL` column with `hidden` 2 and a `STORED`
   one with 3, and no default; the prediction and the harness show the same.
3. **SQLite's rules on definitions**, checked natively with 3.51.0:
   - `generated columns cannot be part of the PRIMARY KEY` and
     `cannot use DEFAULT on a generated column` are prepare errors;
   - the expression resolves over the table's columns, with `no such column` also for
     `rowid`, and `non-deterministic functions prohibited in generated columns`;
   - a generated column may read another generated column, and a loop
     (`generated column loop on "b"`) fails the CREATE TABLE at step;
   - UNIQUE, NOT NULL and CHECK apply to generated columns as to other columns;
   - ADD COLUMN of a `STORED` column fails at step with `cannot add a STORED column`, and
     ADD COLUMN of a `VIRTUAL` one computes its value for the existing rows.
4. **Writes.** An INSERT without a column list takes one value for each column that is not
   generated. Naming a generated column in INSERT is `cannot INSERT into generated column
   "b"`, and in UPDATE `cannot UPDATE generated column "c"`, both prepare errors. Every
   write computes the generated values of the row, in an order that respects their
   dependencies, and stores them with the column's affinity, before the NOT NULL, CHECK
   and unique checks.
5. **Reads.** A generated column reads as a stored column; `*` includes it.
6. **Restrictions.** A form that the model cannot describe stays a restriction, for example
   an expression whose evaluation can fail (a JSON function).

## Tests

- Lean examples: each rule of outcomes 2 to 5; both kinds; a generated column that reads
  another; a loop; INSERT with and without a column list; UPDATE of a column that a
  generated column reads; a UNIQUE and a CHECK on a generated column; ADD COLUMN of each
  kind over rows.
- An authored corpus (`conformance/authored_generated.py`) of these cases, each with a
  kernel proof, recorded as a new corpus.
- The verdict of every corpus: cases that newly agree and none that leave AGREE.
- Mutants: a generated value that is not recomputed on UPDATE, the wrong `hidden` value
  for one kind, and an INSERT without columns that expects a value for a generated column,
  each killed by an authored case.

## Key points

- **Files.** `Resolution/SyntaxDefinitions.lean` (the constraint), `Resolution/Catalog.lean`
  (`CatalogColumn`), `Resolution/Definitions.lean` and `Resolution/AddColumn.lean`,
  `Resolution/InsertCells.lean` and `Resolution/Updates.lean` (the column lists of writes),
  the write paths (`LiteralData.lean`, `RowUpdate.lean`, `UpsertRun.lean`, `Upsert.lean`),
  `belay/sqlite/syntax_definitions.py`, the harness (`conformance/native_metadata.py`
  refuses hidden columns today, `VerifierConformance/Native.lean`, `Predict.lean`,
  `conformance/predict_render.py`).
- **Order of evaluation.** SQLite computes generated columns after the other cells and
  before the constraint checks; a generated column that reads a later generated column
  needs its dependencies first. The model must not use well-founded recursion for the
  order, so that the kernel reduces it.
- **Kernel cost.** A table without generated columns must cost no more kernel time.
- **Stored invariant.** The write-preservation laws state what a stored row satisfies; a
  generated cell joins that invariant, or the laws say why it need not.
