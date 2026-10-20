# `WITHOUT ROWID` tables (ADR 0014, slice 2)

Created 2026-10-19. Status: DONE (pull requests #177 and #178).
Status file: [status](20261019-without-rowid.status.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D4 and "Order and pull
requests"; the [measurement](../experiments/schema-features/README.md).

## Pull requests

- **A (subject):** the model, the frontend, the harness and an authored corpus of
  `WITHOUT ROWID` cases, stacked on slice 1. Nothing under `judge/` or `integrity/`
  changes: the judge already compares `withoutRowid` and the row identity of such a table
  by its primary-key cells (`judge/catalog.py`).
- **B (claims), only if cases newly agree.**

## Outcome

1. **The table option.** `CREATE TABLE ... WITHOUT ROWID` maps to the Syntax IR and to a
   catalog flag. `STRICT` stays a frontend refusal until slice 6.
2. **SQLite's rules, checked natively with 3.51.0:**
   - a table without a PRIMARY KEY is the prepare error `PRIMARY KEY missing on table t`;
   - the key columns are NOT NULL (`table_xinfo` reports them so), and a NULL key fails
     with SQLite's NOT NULL constraint error;
   - no column is a rowid alias, so `INTEGER PRIMARY KEY` takes the written value;
   - `rowid`, `_rowid_` and `oid` that name no column are `no such column` in a query, a
     write or `RETURNING` over the table, not the model restriction `rowid-name`.
3. **Scan order.** A full scan of the table, the source of a query, returns its rows in
   primary-key order, descending for `PRIMARY KEY DESC`, as SQLite's key b-tree does.
4. **Row identity.** The model keeps a hidden rowid per row for its own bookkeeping; no
   result shows it. The harness compares the rows of such a table by their cells, and the
   prediction renders their identity as the primary-key cells, as the recorder does.

## Tests

- Lean examples: the prepare error, a NULL key, an `INTEGER PRIMARY KEY` that is not an
  alias, `rowid` as `no such column`, the scan order of a text key, a composite key and a
  descending key.
- An authored corpus (`conformance/authored_without_rowid.py`) of these cases and of
  INSERT, UPDATE, DELETE, UPSERT and REPLACE on such tables, each with a kernel proof.
- The verdict of every corpus: cases that newly agree and none that leave AGREE.
- Mutants: a scan in insertion order, and a key column that admits NULL, each killed by an
  authored case.

## Key points

- **ADR detail.** D4 states that a row keeps the rowid 0 and that `Table.Valid` states the
  key order. Hidden distinct rowids with a key-ordered scan keep one write path and the
  existing proofs; the slice records this in the ADR as an implementation note.
- **Files.** `belay/sqlite/syntax_definitions.py` (`create_table`, the table option set),
  `Resolution/Syntax.lean`, `Resolution/Catalog.lean` (`CatalogTable`),
  `Resolution/Definitions.lean`, `Resolution/Scope.lean` and `QueryExprs.lean` (rowid
  names), `QueryEval.lean` (the source rows), the harness (`Native.lean`, `Predict.lean`,
  `Json.lean`), `conformance/native_replay.py` (which refuses such tables today) and
  `conformance/predict_render.py`.
- **Migrations.** A CREATE TABLE in a migration needs a PRIMARY KEY here, which is the
  restriction `create-table-constraints` until slice 4, so most cases have the table in
  the schema.
