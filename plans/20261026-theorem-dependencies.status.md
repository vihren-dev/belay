# Theorem dependency report status

Date: 2026-10-26. Status: ACTIVE. Audience: the implementation team.
Task: [dependency report](20261026-theorem-dependencies.task.md).
Base: integration commit `6413afe3ff50`.
Workspace: `/home/codex/work/sqlite-verifier-theorem-dependencies`.

## Progress

- Created an isolated workspace for the owner-authorized implementation.
- Recorded the report contract and acceptance checks before implementation.
- The investigation's disposable Nix exporter established that private imported
  declarations and theorem bodies can be read from the pinned compiled model.
- Implemented the private compiled-environment exporter with exact module
  ownership, separate type/body edges, external targets and source selections.
- Implemented the offline report with dependency/user paths, helper folding,
  source context, module summaries and refactoring candidates.
- Added explicit scope manifests, artifact/source provenance, shared namespace
  loading, optional existing proof costs, a Nix target and usage documentation.
- Self-review fixed direct self-edge display and normalized source hashes to
  match existing proof-cost records. Nix fixture tests exposed ambient compiler
  lookup; the tests now pin the compiler sysroot and poison ambient Lean.
- Initial task review had no must findings. Both scope suggestions were rejected
  with recorded reasons: the owner accepted the proposed report features, and
  browser acceptance checks exercise the controls without adding a new harness.
- Moved the standalone exporter to `tools/theorem_dependency_exporter.lean`.
  It imports only Lean and runs directly, so a compiled library and the CLI's
  former tools-package argument were unnecessary. The documentation package's
  derivation identity now matches the base. Its source and targets are unchanged.

## Evidence

The focused Nix suite passed all 27 tests. A Nix report covers all 928 selected
modules (681 model/codec, 203 surface, 29 text, 15 conformance) and exports
31,098 declarations plus 2,615 external boundary nodes. Counts include generated
declarations. Final artifact paths will be recorded after completion checks.

The implementation review found no must findings and one documentation issue:
the public guide used an internal task label for proof-cost JSON. The guide and
CLI help now give the command that creates the report. The correction review
had no findings. The packaging simplification passed the 27-test Nix suite at
`/nix/store/vsyxsqqxjln57s0li149h98xilq7726x-sqlite-verifier-test-theoremDependencies-1`.

The verdict and scheduled checks passed. An initial full run hit the existing
documentation inventory's 60-second deadline during concurrent cold builds.
Final full checks, infrastructure checks and packaging review are pending.
