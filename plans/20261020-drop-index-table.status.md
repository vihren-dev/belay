# Status: `DROP INDEX` and `DROP TABLE` (ADR 0014, slice 7)

Created 2026-10-20. Status: open.
Task file: [task](20261020-drop-index-table.task.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D7.

## Progress

- 2026-10-20: native behaviour checked with 3.51.0: `no such table` and `no such index`
  (also for an object of the other kind), `IF EXISTS`, `table sqlite_master may not be
  dropped` (also for `sqlite_schema` and with `IF EXISTS`), `index associated with UNIQUE or
  PRIMARY KEY constraint cannot be dropped`, names compared with ASCII case ignored,
  `sqlite_stat1` can be dropped, and ROLLBACK restores a dropped table. `foreign_keys` is
  off by default.

## Remaining

- All outcomes, checks, reviews, CI time, pull requests.
