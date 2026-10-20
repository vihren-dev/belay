# Status: `STRICT` tables (ADR 0014, slice 6)

Created 2026-10-20. Status: open.
Task file: [task](20261020-strict-tables.task.md).
Specification: [ADR 0014](../docs/adr-0014-schema-features.md), D6.

## Progress

- 2026-10-20: native behaviour checked with 3.51.0: the allowed types, with ASCII case
  ignored, and the two prepare errors; `cannot store TEXT value in INTEGER column s.a` with
  extended code 3091 after affinity; NOT NULL first, then the type, then CHECK; `OR FAIL`
  keeps the earlier rows and `OR ROLLBACK` rolls back, while `OR IGNORE` and `OR REPLACE`
  fail; generated columns and `DO UPDATE` are checked; `ANY` keeps text as text; a rowid
  alias still gives `datatype mismatch`; ADD COLUMN with an unknown type fails at step.

## Remaining

- All outcomes, checks, reviews, CI time, pull requests.
