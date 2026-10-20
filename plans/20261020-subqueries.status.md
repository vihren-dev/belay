# Status: subqueries (ADR 0018, slice 1)

Created 2026-10-20. Status: open.
Task file: [task](20261020-subqueries.task.md).
Specification: [ADR 0018](../docs/adr-0018-surface-sql.md), D1.

## Progress

- 2026-10-20: the design of the task file, from the code: `Syntax.Expr` is a nested
  inductive type with `BEq`; `Expr.evaluate clock row` has 56 callers in 9 files.

- 2026-10-20: "the evaluation context" (no change of behavior). `Resolved.EvalContext`
  (`ExprFault.lean`: the clock and the subquery results, with `EvalContext.plain`) replaces
  the clock value in expression and query evaluation, the writes and their laws;
  `runStatement`, `Query.runOn` and the conformance outputs build the plain context of the
  statement's clock value. Every verdict of every corpus is the same as on `main`. Tests:
  the builds of `belay-sqlite`, `sqlite-verifier` and `verifier-conformance`,
  `test_model_package`, `test_lean_categories`, `conformance_query_coverage`,
  `conformance_authored`, the local verdict.

- 2026-10-20: "the resolved subquery forms". `Resolved.Expr` has `exists`, `inQuery` and
  `subquery`, which name a subquery of the statement by index; `Statement.query` holds the
  statement's subqueries. `Subqueries.lean` runs a subquery for an outer row (its sources
  joined after the outer cells) and builds the stratified statement context
  (`statementContext`, the list length as fuel); `Query.runOn`, `statementReady` and the
  conformance outputs use it. `IN` follows SQLite's NULL rules (`inValue`). A scalar subquery
  as a JSON value argument is undescribed (`isSubquery`), because SQLite keeps the JSON
  subtype of its result. Resolution still gives no subqueries. Tests: `SubqueryExamples.lean`
  (each form, correlation at depth one and two, kernel proofs), the builds of the three
  packages, `test_model_package` (the core closure has one more module),
  `test_lean_categories`, `conformance_query_coverage`, `conformance_authored`.

- 2026-10-20: "the rows that SQLite's plan chooses". A scalar subquery reads the first row
  and `IN` the rows of a window, which SQLite's plan can change when rows tie (natively: an
  index on `p(a)` makes `(SELECT b FROM p WHERE a > 0)` give the row of the smallest `a`, not
  the first rowid). `SubqueryRun.firstCertain` and `rowsCertain` (`Query.windowCertain`)
  say whether every permitted order gives the same first values; otherwise the form is
  `Fault.may`, so the statement is not described. `EXISTS` loses its negation flag (`NOT
  EXISTS` is `NOT` of it, as SQLite parses it). `Query.outer` keeps the width of the outer
  row, so a subquery evaluated over the row without cells keeps its cell positions. The
  `mayFail` scan now also covers joined queries. Tests: `SubqueryExamples.lean` (faults of
  scalar subqueries with and without a certain first row, `IN` with `LIMIT`, `EXISTS`).

## Remaining

- All outcomes and tests.
