# Status: translation dependencies and complete local law checks

Created 2026-10-24. Status: OPEN. Specification prepared; implementation has not
started. No owner decision is required for the outcomes currently specified.

Task: [task file](20261024-text-build-boundaries.task.md).
Specifications: [ADR 0016](../docs/adr-0016-model-and-surface.md), D2, and
[ADR 0020](../docs/adr-0020-local-build-loop.md).

## Current evidence

Base: PR #239, `srzmyvyu`, commit `98a07bfec142aacec28c0d3f9d4801dd593515f1`.
The task's relevant-file list names the code and existing checks.
`Translation/Located.lean` imports `Belay.Sqlite.Model`.
The conformance lakefile defaults to `conformance-runner`; the Nix derivation
explicitly builds `VerifierConformance` and `conformance-runner`.
No new build timing or Nix validation result is claimed here.

## Progress

- 2026-10-24: specified the import boundary and the missing local law-library
  check in response to the owner's modularity request. This workspace is
  separate from S4. Task review and implementation are pending.
- 2026-10-24: task review `20261024T115938Z-5fc56924` found no musts and two
  shoulds. The task now states the owner's scheduled-check override and the
  observed law-build failures from the handoff, and removes the proposed
  failure-injection harness. The existing local-loop test remains the check of
  the recipe. Implementation is pending.
- 2026-10-24: review `20261024T120211Z-4d34419d` found no musts and requested
  a durable record of the handoff evidence. The source is the owner-provided
  `/home/codex/work/HANDOFF-adr17-20261024.md`, section "How the work is done":
  "`just dev-build` builds only the conformance runner, not the law modules, and
  `test-full` failed twice because of this." This is a reported observation;
  that handoff supplies no run IDs, so this status does not claim independently
  verified failure logs. The task's target correction is independently supported
  by the current recipe and the Nix library targets recorded above.
  The same source, "Owner rules for this work", says: "Run only the relevant
  mutant tests, by name (`-k`). Never run `just test-scheduled` or
  `just test-mutants` locally; run `just test-scheduled-checks` at the end of a
  task." This is the owner instruction that overrides the older cadence table.
