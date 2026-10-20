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

## Remaining

- All outcomes and tests.
