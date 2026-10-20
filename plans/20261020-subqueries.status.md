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

- 2026-10-20: "subqueries in SELECT, from SQL text". The frontend lifts the subqueries of a
  `SELECT` into the statement's list (`belay/sqlite/syntax_subqueries.py`, in the order of
  their text, each with the query around it), and refuses them in other statements.
  `Syntax.Expr` has `exists`, `inQuery` and `subquery`; `Syntax.Statement.select` has
  `subqueries` (child 8). Scope sources have a depth: a name resolves in its own query
  first, then outward, and `*` sees only the query's own sources. `SelectResolution.lean`
  resolves the scopes outward-in and the bodies inward-out, so a query knows the shapes of
  its subqueries (`SubqueryShapes.lean`: column count, affinity and collations of the first
  result column, lowest cell read). New restrictions: `subquery-here`, `outer-aggregate`,
  `subquery-fallible-call`; new prepare error `sub-select returns N columns - expected 1`.
  An alias of an outer query in a subquery's `WHERE` is `alias-in-expression`. Native
  probes: the recorder cannot observe tie groups for a nested `LIMIT` or an `ORDER BY` key
  that is not a projected name, so the authored cases avoid both. Tests:
  `SubqueryResolutionExamples.lean`, `tests/syntax_subqueries_test.py`,
  `conformance/authored_subqueries.py` (20 cases, all agree with kernel proofs), the
  restriction examples, `test_model_package` (175 core modules), `test_lean_categories`,
  `conformance_query_coverage`, `conformance_authored`, the syntax tests.

- 2026-10-20: "eponymous table-valued functions". The local verdict of the previous commit
  found a disagreement: `json101-17.1` reads `FROM json_each` without arguments inside a
  subquery, which SQLite reads as its eponymous table-valued function, and the model gave
  `no such table`. A missing table named `json_each`, `json_tree`, `dbstat` or `pragma_...`
  is now the restriction `table-function` (`eponymousName`, checked natively). The local
  verdict after it: no case leaves AGREE; 7 cases of v5 and 2 of v4 newly agree. Of the v5
  cases whose restriction changed, 22 have a subquery in a write, 15 a compound subquery,
  6 a derived table, 5 an outer aggregate and 4 `HAVING`.

## Remaining

- All outcomes and tests.
