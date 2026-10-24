# Status: S6 execution and proof contracts

Created 2026-10-24. Status: OPEN. Implementation has not started.
Task: [task file](20261024-s6-execution-contracts.task.md).
Specs: ADR17's accepted strong equivalence and the checked S6 foundations.

## Prerequisites and scope

The owner accepted full actual and branch-outcome equivalence on 2026-10-24.
The prototype proves the relevant generic transformer laws, but its original
instance rejects SQL errors and its equivalence omits failed alternative traces.
Production must support conditional triples and retain those traces explicitly.

Implementation waits for task review, final S4 interfaces and an available
agent/build slot. Its modules can remain separate from query-context work.
The accepted quiet observation view affects later migration patterns,
not these complete-execution semantics. No production or acceptance result
is claimed by this task file.

## Progress

- 2026-10-24: specified exact execution branches, operationally sound Std.Do
  primitives, conditional/total success bridges and compositional equivalence.
  Two acceptance parts retain the ordinary model interpreter and S4 contracts.
  The public assertion/pattern/automation task remains to be specified.
- 2026-10-24: review `20261024T144607Z-9eeac73e` found no musts and two
  shoulds about unavailable inputs in the planning tree. The task now names
  the unmerged S4 and prototype workspaces and exact reviewed commits. Also
  replaced a reference to transaction helpers with the existing explicit
  BEGIN/COMMIT/ROLLBACK programs; ADR17 still defers withTransaction.
- 2026-10-24: follow-up review `20261024T144839Z-5684010b` has no findings.
  Implementation remains unassigned and waits for final S4 interfaces.
