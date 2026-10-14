# Writes with output, slice 3a of ADR 0012

Created 2026-10-14. Status: IN PROGRESS.
Specification: [ADR 0012](../docs/adr-0012-query-semantics.md), "Slices", item 3,
narrowed by the owner on 2026-10-14 to the part that keeps writes literal (slice 3a).
Writes whose values or filters depend on the row (`SET v = v + 1`, a general `WHERE`)
change the data-domain obligations of the verification target; they wait for an
amendment of ADR 0012, which is drafted separately. Related: slices 1 and 2
([task](20261013-single-table-queries.task.md), [task](20261013-query-numbers.task.md));
ADR 0005 section 3.1 for `RETURNING` output; ADR 0011 for claims.

## Plan

Two pull requests, as for slices 1 and 2:

- **Pull request A (subject):** syntax, resolution with its specification, the
  `RETURNING` output, the frontend mapping, authored coverage cases with kernel
  proofs, mutants and their corpus writer. No change under `judge/` or `integrity/`.
- **Pull request B (judge, owner approval):** the coverage corpus is frozen and
  claimed, and the corpus cases that newly agree are added to `mustAgree`.

## Outcome

1. **Constant expressions in writes.** A `VALUES` item and a `SET` value may be any
   expression of slices 1 and 2 that names no column: arithmetic, `CAST`,
   `COALESCE`, comparisons, logical operators and REAL literals. Resolution
   computes its value with the query semantics. The value is then stored as
   today: it must be one that the column affinity keeps unchanged, else the write
   is a model restriction. The resolved statement stays literal, so the
   data-domain obligations and the verification target do not change.
2. **Row-dependent writes stay restricted.** A column reference in a `SET` value or
   in a `VALUES` item, and an `UPDATE` filter other than `column = integer`, remain
   model restrictions, with messages that say what to write instead.
3. **`RETURNING`.** `INSERT … VALUES … RETURNING` and `UPDATE … RETURNING` with result
   columns as in `SELECT` (`*`, expressions over the written row, aliases), naming
   as SQLite names them, and SQLite's prepare errors (`no such column`, `misuse of
   aggregate function`). An `INSERT` returns one row per inserted row; an `UPDATE`
   one row per changed row, with the new values. The rows compare as a multiset
   (ADR 0005). A write that fails returns no rows.
4. **Statements.** `RETURNING` changes no state and no change count; the execution
   semantics and the verification target do not change. The output of a write is
   its change count and its `RETURNING` columns and rows.
5. **Evidence.** Authored coverage cases for each rule, with neighbors, agree with
   native SQLite and have kernel proofs; the mutants below each change a verdict;
   the verdict counts of the claimed corpora do not go down.

## Tests

- Frontend mapping of `RETURNING` on `INSERT` and `UPDATE`, of expressions in
  `VALUES` and `SET`, and refusal of the forms outside the slice, with byte ranges.
- Lean examples and specification proofs: a constant expression in `VALUES` stores
  the value that the query semantics gives it; `RETURNING` of an `INSERT` gives one
  row per inserted row with the stored values.
- Authored coverage cases: `RETURNING *`, columns, expressions and aliases on
  `INSERT` (one and several rows, omitted columns) and `UPDATE` (rows that match,
  none that match); a failing write with `RETURNING`; the prepare errors in
  `RETURNING`; constant expressions in `VALUES` and `SET` with each storage class,
  including a value that the affinity would convert (a restriction).
- Mutants, each changing the verdict of a case: `RETURNING` of an `UPDATE` with the
  old values; `RETURNING` rows for every row instead of the matched ones; a
  `RETURNING` row for a failing write; `RETURNING` names that ignore the defined
  name; a constant expression stored without its value computed (for example,
  `1 + 2` stored as 1).

## Key points for the implementer

- **Writes are literal today, and stay literal.** `Resolved.Statement.insert` holds
  full rows of values, `update` holds `(position, value)` assignments and a filter
  `(position, value)`. `LiteralData.insertReady` and `updateReady` check that each
  stored value is `lossless` for its column, and `Contract.lean` requires them
  through `SupportedSql`. Folding constant expressions at resolution keeps all of
  this. `RowSpec.storedValue_ok` and the rules in `RowSpec.lean`,
  `UpdateRules.lean` and `ErrorKinds.lean` follow the branch structure of
  `resolveInsert` and `resolveUpdate`; changes to those functions need the proofs
  updated.
- **`RETURNING` is output only.** `Outcome` carries no rows, and `Contract.lean`
  (owner review) does not need to change. `RETURNING` can be a field of the
  resolved write that `step` ignores, or a separate piece of the statement that
  only `Outputs.statementOutput` reads. Constructor arity changes break explicit
  patterns in `Laws.lean`, `Preservation.lean`, `SqlExamples.lean` and the mutant
  texts in `conformance/mutation_check.py` and `tests/conformance_mutation_test.py`.
- **Naming and errors.** SQLite names `RETURNING` columns as `SELECT` result
  columns (checked natively on 3.51.0: `RETURNING b` on a column `B` is named `B`;
  `rowid` and `oid` are both named `rowid`; `count(*)` gives `misuse of aggregate
  function count()` and a missing name `no such column` at prepare). Reuse
  `resolveResultColumn`; rowid names stay a restriction.
- **`UPDATE` rows.** `RETURNING` of an `UPDATE` evaluates on the new row of each
  row that the filter selects (`LiteralData.selected`, `LiteralData.assign`).
- **Frontend.** `INSERT … RETURNING` parses as `upsert ::= RETURNING selcollist`;
  `UPDATE … RETURNING` as `where_opt_ret`. `syntax_writes.py` refuses both today.
  Expressions in writes go through `syntax_expressions.expression`, which refuses
  arithmetic and calls; `syntax_queries.query_expression` maps them but its file is
  at 197 lines, so move code before adding to it.
- **Parameters.** Most existing corpus cases with `RETURNING` bind parameters,
  which the model does not support (`Case.lean`, `classifyCase`); they stay
  `MODEL_UNSUPPORTED`. The coverage cases use literals.
- **File size.** `Resolution/Writes.lean` (173 lines) and `Resolution/Examples.lean`
  (176) are near the limit; put new rules and examples in new modules.
