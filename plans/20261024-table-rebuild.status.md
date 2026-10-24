# Status: query inserts and ALTER table rebuild

Created 2026-10-24. Status: OPEN. Implementation has not started.
Task: [task file](20261024-table-rebuild.task.md).
Specs: ADR19 D4/slice 5, ADR17 S6 and ADR22 preservation contracts.

## Accepted decision and prerequisites

The owner accepted exact INSERT SELECT streaming/materialization, including
error precedence and partial writes, on 2026-10-24. ADR19 D4 records the native
overflow-versus-unique-conflict example; the previous always-materialize rule
is superseded. This is a planning/native-source observation, not task acceptance.

Implementation waits for all query-source parts, including the final view and
CTE representation, and coordinated FK atom interfaces. It must extend those
representations and preservation laws. S6's universal rebuild proof is separate.

## Progress

- 2026-10-24: specified complete D4 scope, three acceptance parts, native
  differential cases and modular contracts. Await independent task review.
  No new corpus claim, production source change or acceptance result is claimed.
