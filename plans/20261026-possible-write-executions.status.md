# Status: possible write executions

Created 2026-10-26. Status: OPEN. Implementation has not started.
Task: [task file](20261026-possible-write-executions.task.md).
Specs: ADR 0019 D4 and its amendment of 2026-10-25, ADR 0012's clarification
of 2026-10-25, and the table-rebuild task.

## Decisions

- 2026-10-25 (owner): plan-dependent INSERT SELECT behavior is represented by
  possible write executions (ADR 0019 D4 amendment).
- 2026-10-26 (owner): the execution interface is a separate task before INSERT
  SELECT, proved on all existing statements as the singleton case, with no new
  SQL. The table-rebuild agent reported the reach of the change.

## Progress

- 2026-10-26: task specified.
