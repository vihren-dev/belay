# Status: DISTINCT, HAVING and aggregates inside expressions (ADR 0018, slice 3)

Created 2026-10-21. Status: DONE (2026-10-21).
Task file: [task](20261021-distinct-having.task.md).
Specification: [ADR 0018](../docs/adr-0018-surface-sql.md), D3.

## Progress

- 2026-10-21: the task file, from native probes and the code of slices 1 and 2.

- 2026-10-21: "aggregates in expressions, HAVING and DISTINCT". A resolved query lists its
  aggregates (`Query.aggregates`), and an expression names one by index
  (`Expr.aggregateValue`), which evaluation reads from the group's context
  (`Query.groupContext`, `EvalContext.aggregates`); `QueryResults.lean` holds the records with
  `HAVING` and `DISTINCT`. Resolution collects the aggregate calls of the result columns,
  `HAVING` and `ORDER BY` (`QueryAggregates.lean`), checks that `HAVING` and `ORDER BY` read
  only grouping terms and aggregates (`Resolved.Expr.grouped`), and gives SQLite's `HAVING
  clause on a non-aggregate query`. `SELECT DISTINCT` whose equal rows differ is not described
  (`Query.distinctCertain`); ADR 0018 D3 is amended for it. New restriction
  `distinct-order-by`; `aggregate-in-expression` now covers a fallible call over an aggregate
  and `aggregate-order-by` a term outside the grouping terms. The syntax holds `having` and
  `distinct`, which the frontend writes only when present (`Codec/SyntaxJson.lean` reads a
  missing one as absent). The derived `BEq` of `Syntax.Expr` does not reduce in the kernel, so
  the aggregate lookup uses a structural equality (`SyntaxEquality.lean`); with the derived one,
  the kernel proofs failed or timed out. Tests: `Resolution/GroupExamples.lean`, the syntax
  tests, `conformance/authored_distinct_having.py` (12 cases, all agree with kernel proofs, each
  in about a second), three mutants, each killed, corpus writer 44, `test_model_package` (180
  core modules).

- 2026-10-21: "the end of the slice". Review fixes: SQLite decides an aggregate query from
  `GROUP BY` and the result columns, so `HAVING` and an `ORDER BY` aggregate of another query are
  its prepare errors, `HAVING` is checked after the result columns, and `GROUP BY 1` over a
  result column with an aggregate is `aggregate functions are not allowed in the GROUP BY
  clause`. The local verdict found frozen case `select1-2.3` (`SELECT Count() FROM test1`):
  `count()` without an argument is an aggregate call now. Tests that used `SELECT DISTINCT 1` as
  unmodeled SQL use `SELECT 1 UNION SELECT 2`; the authored catalog has 30 agreeing cases.
  Local verdict: no case leaves AGREE; against slice 2, 92 cases of v5, 44 of v4 and 4 of v3
  newly agree (against `main`: 234, 68 and 25). `just test-full` passes. DONE.

## Remaining

- PR A and PR B come at the end of ADR 0018.
