# Status: the aggregates group_concat, string_agg and total (ADR 0015, slice 5)

Created 2026-10-20. Status: open.
Task file: [task](20261020-aggregates.task.md).
Specification: [ADR 0015](../docs/adr-0015-functions.md), D7.

## Progress

- 2026-10-20: SQLite 3.51.0's `groupConcatStep`, `groupConcatFinalize` and `totalFinalize`
  read; native: the rows of a group keep their scan order with `GROUP BY`, and the separator
  is that of each row (`string_agg(v, w)` is `b2a1c`).

## Remaining

- All outcomes and tests.
