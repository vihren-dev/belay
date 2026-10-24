# Status: S7 proof-cost collector prototype

Created 2026-10-24. Status: OPEN. Assigned; implementation has not started.
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
- Assigned to `s4_part1` in isolated `s7-proof-cost`, based on reviewed S4
  source `2e51a0ae`. S4's broad acceptance remains open; integrate its final
  published boundary before prototype acceptance. Root coordinates those gates.
  This carries the existing task without a new scope decision or task-file edit.
- A read-only preflight identified native `Elab.definition.value` traces as a
  candidate for both sync and async body elaboration. An imported declaration
  wrapper could delegate to `elabDeclaration`, retain completed snapshot/trace
  tasks, and export plain records through a persistent environment extension.
  Its export callback runs after async threads join. No collector has compiled.
- The experiment must enable the trace class to retain exact-zero nodes,
  preserve internal heartbeat units, and flag Float precision loss. Async
  diagnostics can hold consumed traces, so inspect structured messages and
  trace trees. Command linters restore their environment; updates there alone
  do not persist. Body traces exclude headers and later kernel checking, so
  their counts cannot be described as total proof costs. Missing data is not zero.
- Automatic approval rejected shell authorization for the new workspace even
  though its shell files match authorized `s4-run`. Explicit owner approval is
  pending. Source inspection can continue; no build has run in this workspace.
