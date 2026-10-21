# DISTINCT, HAVING and aggregates inside expressions (ADR 0018, slice 3)

Created 2026-10-21. Status: DONE (2026-10-21).
Status file: [status](20261021-distinct-having.status.md).
Specification: [ADR 0018](../docs/adr-0018-surface-sql.md), D3.

## Process

As for slices 1 and 2: local jj commits with the tests that touch each one; at the end of the
slice the local verdict, the corpus, and `just test-full`.

## Outcome

1. **Aggregates inside expressions.** In the result columns, `HAVING` and `ORDER BY` of a
   query, an aggregate may be part of an expression (`count(*) + 1`, `max(v) - min(v)`), with
   the value of the aggregate over the group's rows, also over an empty group. An aggregate
   in `WHERE` or in the argument of another aggregate stays SQLite's `misuse of aggregate
   function`, and one in `GROUP BY` stays `aggregate functions are not allowed in the GROUP BY
   clause`.
2. **`HAVING`**, with and without `GROUP BY`: it keeps the groups for which it is true. A query
   with `HAVING` and no aggregate and no `GROUP BY` is SQLite's prepare error `HAVING clause on
   a non-aggregate query`.
3. **`ORDER BY` of an aggregate query** by an expression of grouping terms and aggregates, not
   only by result column numbers and aliases.
4. **`SELECT DISTINCT`**: one row of each set of rows that compare equal under each result
   column's collation, before `ORDER BY`, `LIMIT` and `OFFSET`. When the rows of such a set
   differ (for example `'a'` and `'A'` under `NOCASE`), SQLite's plan chooses the one it keeps,
   so the statement is not described (ADR 0018 D3, amended 2026-10-21).
5. **Restrictions.** A column outside the grouping terms and the aggregates in a result column,
   in `HAVING` or in `ORDER BY` of an aggregate query stays the restriction `bare-column`;
   `DISTINCT` inside an aggregate call stays refused.

## Tests

- Lean examples of each outcome, with kernel proofs.
- An authored corpus (`conformance/authored_distinct_having.py`), each case with a kernel
  proof, recorded as corpus 44: aggregates in arithmetic and comparisons, over groups and
  over an empty table; `HAVING` with and without `GROUP BY`, with an aggregate that is not a
  result column; `ORDER BY` by an aggregate; `DISTINCT` over integers, text with `NOCASE`
  whose duplicates are equal, NULLs, and with `ORDER BY` and `LIMIT`; the prepare errors of
  `HAVING` on a non-aggregate query and of a nested aggregate.
- The verdict of every corpus: cases that newly agree and none that leave AGREE.
- Mutants: `HAVING` that keeps a group for which it is NULL, an aggregate in an expression
  computed over the first row of its group only, and `DISTINCT` that keeps every NULL row
  (SQLite's `DISTINCT` treats NULLs as equal); each killed by an authored case. A `DISTINCT`
  that compares with `BINARY` instead of a column's collation is no mutant: only rows that
  differ but compare equal tell the two apart, and the model does not describe them.

## Key points

- **An aggregate inside an expression names an aggregate of its query.** The resolved query
  lists its aggregates; an expression names one by its index, and evaluation computes the
  list for each group before it evaluates the result columns, `HAVING` and the sort keys of
  the group. `Resolved.Aggregate` holds expressions, so an expression cannot hold an
  aggregate without one mutual type; the index avoids it, as subqueries do in slice 1.
- **The syntax of an existing record must not change.** Frozen records hold `select` without
  `having` and `distinct`, as slice 1 found for `subqueries`: the frontend writes them only
  when present, and the codec (`Codec/SyntaxJson.lean`) reads a missing one as absent.
- **Checked natively** over `t(g, v INTEGER, s TEXT COLLATE NOCASE)` with the rows
  `(1, 10, 'a')`, `(1, 20, 'A')`, `(2, 5, 'b')`, `(3, NULL, 'c')`: `SELECT g, count(*) + 1, sum(v) * 2,
  max(v) - min(v) ... GROUP BY g` gives `1|3|60|10`, `2|2|10|0`, `3|2||`; `SELECT count(*) FROM t
  HAVING count(*) > 1` gives 4; `SELECT v FROM t HAVING v > 1` is `HAVING clause on a
  non-aggregate query`; `SELECT DISTINCT s ... ORDER BY 1` gives `a`, `b`, `c` (the first of
  `'a'` and `'A'` in the scan); `SELECT count(*) + 1, max(v) IS NULL FROM t WHERE 0` gives `1|1`.
- **Files.** `Resolution/QueryForm.lean` (the query's aggregates, `HAVING` and `DISTINCT`),
  `Resolution/Queries.lean` and `Resolution/QueryTerms.lean` (the grouped-expression check),
  `Resolution/ExprForms.lean` (`aggregateIssue`), `QueryEval.lean`, `QueryRun.lean`, the
  frontend `belay/sqlite/syntax_select.py`, and every exhaustive match over the resolved
  expression type.
