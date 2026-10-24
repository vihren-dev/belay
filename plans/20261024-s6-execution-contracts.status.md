# Status: S6 execution and proof contracts

Created 2026-10-24. Status: OPEN. Implementation has not started.
Task: [task file](20261024-s6-execution-contracts.task.md).
Specs: ADR17's accepted strong equivalence and the checked S6 foundations.

## Prerequisites and scope

The owner accepted full actual and branch-outcome equivalence on 2026-10-24.
The prototype proves the relevant generic transformer laws, but its original
instance rejects SQL errors and its equivalence omits failed alternative traces.
Production must support conditional triples and retain those traces explicitly.

Final S4 interfaces and the prototype are published. The task is refreshed
for assignment to `text_build_boundaries` in a separate workspace on PR #248.
Its modules remain separate from FK and query-context implementation work.
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

- 2026-10-24: refreshed the handoff to published #248 `e3d6aa38`, which contains
  completed S4 #244 and S6 prototype #246. Removed stale workspace and pending
  validity-check references. Made the accepted fresh-run helper/ordinary-triple
  equivalence explicit. The owner accepted that contract earlier; this refresh
  adds no scope decision. The FK owner confirmed that generic branch/WP/equality
  work can proceed independently while remaining FK checks run. Assignment
  follows review of this refresh; heavy checks require the coordinator's slot.
- Handoff refresh `7e855ae9` passed independent review
  `20261024T204324Z-7e855ae9` with no findings. Root verified the named completed
  sources in published #248; the planning tree itself retains older model code.
  Assigned to `text_build_boundaries` in `sqlite-verifier-s6-execution` on
  `e3d6aa38`, alongside its independent FK acceptance work. Implementation owns
  new surface execution-context/branch/WP/equivalence modules and their fixtures.
  Shared barrel and suite-registration additions must stay narrow; S5 owns its
  counterexample/search modules. No production implementation is claimed yet.
