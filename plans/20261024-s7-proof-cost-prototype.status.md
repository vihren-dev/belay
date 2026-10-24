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
  imported-data and growth checks. Review `20261024T141219Z-2ae528dd` had no
  musts and one should: comparison implementation precedes its settled contract.
  Kept only the written baseline sketch and actual measured-growth fixture.
  Follow-up review 20261024T141307Z-82085ddd had no findings; assignment remains
  pending.
  The production cost task follows the measured findings; files/freshness and
  checked doc blocks remain separate tasks toward the same ADR17 completion.
- Read-only follow-up inspected the pinned Trace/CoreM/MutualDef APIs. Native
  profiler heartbeat mode and named async proof traces are candidate inputs.
  No compiling collector, attribution measurement or imported registry was
  tested. The task now names this evidence without choosing an implementation.
- Review 20261024T153725Z-cca27596 found no musts or shoulds in the additional
  source inputs. The experiment and production cost task remain open.
