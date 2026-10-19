# Collations (ADR 0014, slice 3)

Created 2026-10-19. Status: open.
Status file: [status](20261019-collations.status.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D3 and owner decision 1; the
[measurement](../experiments/schema-features/README.md).

## Pull requests

- **A (subject):** the model, the frontend, the harness and an authored corpus of collation
  cases, stacked on slice 2. Nothing under `judge/` changes: the judge compares the
  collation of each index column already (`judge/catalog.py`).
- **B (claims), only if cases newly agree.**

## Outcome

1. **Syntax.** `COLLATE name` on a column and `expr COLLATE name` in an expression map to
   the Syntax IR. A collation in a key of a table constraint stays a frontend refusal.
2. **Three collations.** `BINARY`, `NOCASE` and `RTRIM`, with ASCII case of the name
   ignored. Any other name is SQLite's prepare error `no such collation sequence: %s` in a
   column definition and an index term, and the restriction `unknown-collation` in any
   other expression: SQLite looks the name up only where it uses the collation, and its
   query planner decides some of those uses (checked natively; amended 2026-10-19).
   Checked natively with 3.51.0:
   - `NOCASE` compares TEXT with ASCII letters folded (`'Ä'` and `'ä'` differ);
   - `RTRIM` compares TEXT after removing trailing spaces (`'a '` is less than `'a\t'`);
   - a collation changes only TEXT comparisons; `1 COLLATE NOCASE` is the integer 1.
3. **The catalog.** A column has a collation (`BINARY` by default). An index term has the
   collation of an explicit `COLLATE`, else of its column, else `BINARY`. The unique keys
   of the primary key and of UNIQUE constraints compare under their columns' collations.
4. **Resolution decides each collation once**, by SQLite's rules (`sqlite3ExprCollSeq`,
   `sqlite3BinaryCompareCollSeq`), and the resolved form stores it:
   - a comparison: an explicit collation of the left operand, else of the right, else the
     column collation of the left operand, else of the right, else `BINARY`;
   - an `ORDER BY` and a `GROUP BY` term, and `min` and `max`: the collation of their
     expression;
   - `COLLATE` passes through unary plus and `CAST` to the operand, and the collation of
     a column reference is its column's;
   - the equality that `USING` and `NATURAL` make: the collation of the left-most left
     column of the name (a coalesce of left columns has the collation of its first
     argument, checked natively).
   - a `GROUP BY` term may be a column name under one `COLLATE`.
5. **Execution compares through the collation** wherever it compares values: comparison
   operators, sorting, grouping, `min` and `max`, unique keys (also partial and expression
   keys), and the scan order of a `WITHOUT ROWID` table.
6. **The harness and predictions** show the collation of each index column, as the
   recorder does.

## Tests

- Lean examples: each rule of outcome 4; `NOCASE` and `RTRIM` comparisons; ORDER BY,
  GROUP BY and `min`/`max` over a `NOCASE` column; a `NOCASE` UNIQUE column that refuses
  `'A'` after `'a'`; an index term with `COLLATE`; the prepare error.
- An authored corpus (`conformance/authored_collations.py`) of these cases, each with a
  kernel proof.
- The verdict of every corpus: cases that newly agree and none that leave AGREE.
- Mutants: a comparison that ignores the collation, the right operand's collation chosen
  first, and a key that compares with `BINARY`, each killed by an authored case.
- The laws of sorting (`QueryLaws.lean`) keep their proofs: every collation is
  `compareValues` of a key of the value, which keeps `Std.TransCmp`.

## Key points

- **Representation.** `Collation.key : Value → Value` (identity, ASCII-folded TEXT,
  TEXT without trailing spaces) and `Collation.compare c a b = compareValues (c.key a)
  (c.key b)`. `BINARY` is the identity, so its kernel cost stays.
- **Files.** `Comparison.lean` (`Comparison.apply`), `QueryEval.lean` (aggregates,
  grouping, `compareTerm`, `compareSort`, `Table.scanRows`), `LiteralData.lean`
  (`keyCellsEqual`), `Resolution/QueryForm.lean` (`compare`, `SortKey`, aggregates),
  `Resolution/QueryExprs.lean`, `Resolution/Queries.lean`, `Resolution/JoinUsing.lean`,
  `Resolution/Keys.lean`, `Resolution/IndexTerms.lean`, `Resolution/Definitions.lean`,
  `belay/sqlite/syntax_definitions.py`, `syntax_queries.py`, the harness and
  `conformance/native_metadata.py` (which refuses a collation other than `BINARY` today).
- **ON CONFLICT targets.** Checked natively: a target without `COLLATE` matches a key of
  any collation, so the target matching stays; `COLLATE` in a target stays a frontend
  refusal.
