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
