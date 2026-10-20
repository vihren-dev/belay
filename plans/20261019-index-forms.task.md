# Index forms: expression keys, partial indexes and indexes that run (ADR 0014, slice 1)

Created 2026-10-19. Status: open.
Status file: [status](20261019-index-forms.status.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D1 and "Order and pull
requests"; the [measurement](../experiments/schema-features/README.md).

## Pull requests

- **A (subject):** the model, the frontend, the conformance harness and an authored corpus
  of index cases. It is stacked on the ADR 0014 pull request (#170) and changes nothing
  under `judge/` or `integrity/`; the judge already compares partial indexes, expression
  keys and sort orders (`judge/catalog.py`).
- **B (claims), only if cases newly agree:** the new authored corpus and the upstream cases
  that agree join `judge/claims.json`, with a new judge lock (owner approval).

## Outcome

1. **CREATE INDEX keys are terms.** A key term is an expression with an optional `ASC` or
   `DESC`, and the index has an optional `WHERE` filter, in the Syntax IR and in the
   catalog (`CatalogIndex`). A term that is an unqualified column name is a column key; any
   other term is an expression over the table's row.
2. **Resolution follows SQLite's prepare errors for index forms**, checked natively:
   - `no such column` for an unknown name in a term or in the filter;
   - `the "." operator prohibited in index expressions` for a qualified name in a term (a
     qualified name of the table in the filter is allowed);
   - `non-deterministic functions prohibited in index expressions` and
     `... in partial index WHERE clauses` for `CURRENT_TIME`, `CURRENT_DATE` and
     `CURRENT_TIMESTAMP`;
   - `misuse of aggregate function` for an aggregate in a term or the filter;
   - `rowid` in a term is `no such column`.
3. **Forms that the model does not describe stay restrictions, with exact reasons:** a date
   and time function in a term or the filter (SQLite refuses it only when a row is
   written), a JSON function (it can fail while a row is written), a string literal as a
   term (SQLite reads `'b'` as the column `b`), a rowid name in the filter, `COLLATE` in a
   term (slice 3), and a sort order in a table constraint key.
4. **One unique-key function.** `Catalog.uniqueKeys` gives every unique key of a table, the
   primary key, the UNIQUE constraints and the unique indexes, as one form: its terms and its
   optional filter. Two rows conflict on a key when the filter is true for both (NULL is not
   true), every term is equal under `BINARY` ({name}`keyCellsEqual`), and no term is NULL.
   INSERT, UPDATE, UPSERT and REPLACE use it. An `ON CONFLICT` target matches only a key of
   columns without a filter, as in SQLite.
5. **A CREATE INDEX that runs.** In a script, CREATE INDEX builds the index over the existing
   rows. A unique index whose key has a conflict among those rows fails the statement with
   SQLite's constraint error, and the catalog stays the same. The restriction
   `create-index-runs` goes.
6. **The harness and the predictions show the index forms.** The native cases of the
   harness carry expression keys (no column position), sort orders and the partial flag,
   and the model's prediction renders them in SQLite's `index_list` and `index_xinfo` form,
   so the judge compares them as it compares native observations.

## Tests

- Lean examples of resolution: each prepare error and restriction of outcomes 2 and 3, a
  column key, an expression key, a filter, and `DESC`.
- Lean examples of execution: a partial unique index that admits two rows outside its
  filter and refuses two inside it; an expression index that refuses rows equal under the
  expression; a CREATE UNIQUE INDEX that fails over existing duplicates and keeps the
  catalog; REPLACE and UPSERT over a partial index.
- An authored corpus (`conformance/authored_indexes.py`) of these cases against the pinned
  native SQLite, each with its kernel proof in the model suite.
- The verdict of every corpus: cases that newly agree and no case that changes from AGREE.
- Mutants: a filter that is ignored, an expression key read as its first column, and a
  CREATE INDEX that runs without its uniqueness check, each killed by an authored case.

## Key points

- **Files.** `Resolution/Syntax.lean` (`createIndex`), `belay/sqlite/syntax_definitions.py`
  (`create_index`), `Resolution/Catalog.lean` (`CatalogIndex`, `uniqueKeys`),
  `Resolution/Definitions.lean` (`resolveCreateIndex`), `LiteralData.lean` (`keyEqual`,
  `uniqueRows`, `constraints`), `Upsert.lean`, `RowUpdate.lean`, `Resolution/Upserts.lean`
  (`targetKey`), `Resolution/ConflictPolicy.lean` (`keyAlgorithms`), `Execution.lean`
  (`step`), `StatementStep.lean`, `Model.lean` (`CatalogObject.supported`),
  `verifier-conformance` (`Native.lean`, `Predict.lean`, `Json.lean`),
  `conformance/native_metadata.py` and `conformance/predict_render.py`.
- **Evaluation of a key.** `LiteralData` imports only `Model`; evaluating expression keys
  needs `ExprEval`, so the key functions move after it. Key expressions read no clock, so
  they evaluate at clock 0.
- **Frozen cases.** `conformance/cases/*.json` (version 4) carry native indexes as
  `{name, columns, unique}`; the harness must still decode them (a column list of numbers,
  no sort order, not partial).
- **Positions that a key reads.** UPDATE's restriction `row-dependent-key` and the UPSERT
  checks read the positions of the keys; for an expression key they are the positions that
  its terms and its filter read.
- **Proofs.** The lemmas of `LiteralPreservationLaws.lean` are generic in the key and should
  keep their proofs; `CatalogObject.supported` and `Catalog.Valid` gain the conditions that
  an index's terms and filter read only positions of its table.
