# Status: NOT IN and correlated NOT EXISTS query laws

Created 2026-10-27. Status: OPEN.
Task: [task file](20261027-not-in-subquery-laws.task.md).
Specs: ADR 0017 S4 and S6; the S6 automation task and its part 2 open point
"notBlocked".

## Decisions

- 2026-10-27 (owner): the universal `notBlockedIn ≈ notBlockedEx` claim gets
  general NOT IN / correlated NOT EXISTS query laws in this separate task, not
  a guide change.

## Progress

- 2026-10-27: task specified on the open PR stack (after table rebuild part 2,
  PR #279). The implementation starts after S6 automation part 2 is published,
  because it extends that part's `notBlocked` fixture.
