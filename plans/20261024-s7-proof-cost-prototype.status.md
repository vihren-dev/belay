# Status: S7 proof-cost collector prototype

Created 2026-10-24. Status: OPEN. Implementation has not started.
Task: [task file](20261024-s7-proof-cost-prototype.task.md).
Spec: ADR17 S7's checker and target stable-proof experience.

## Current evidence

The S7 source audit found no surface collector or compiled proof-cost registry.
Pinned Lean's withHeartbeats counts a computation in internal units, 1000 per
user-facing unit. Async completion and per-declaration attribution remain to
be demonstrated. No production measurement or baseline guarantee is claimed.

## Progress

- 2026-10-24: specified the bounded attribution/coverage experiment and its
  imported-data and growth checks. Await independent review and assignment.
  The production cost task follows the measured findings; files/freshness and
  checked doc blocks remain separate tasks toward the same ADR17 completion.
