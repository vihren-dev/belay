# Status: subqueries (ADR 0018, slice 1)

Created 2026-10-20. Status: open.
Task file: [task](20261020-subqueries.task.md).
Specification: [ADR 0018](../docs/adr-0018-surface-sql.md), D1.

## Progress

- 2026-10-20: the design of the task file, from the code: `Syntax.Expr` is a nested
  inductive type with `BEq`; `Expr.evaluate clock row` has 56 callers in 9 files.

## Remaining

- All outcomes and tests.
