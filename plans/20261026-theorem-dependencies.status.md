# Theorem dependency report status

Date: 2026-10-26. Status: DONE. Audience: the implementation team.
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
declarations. The report and its complete JSON data are at
`/nix/store/qlc4jzjxq83i9s8lkj5kxl80bgxhizfn-sqlite-verifier-theorem-dependencies`.
The workspace links that output at `build/theorem-dependencies`.

The implementation review found no must findings and one documentation issue:
the public guide used an internal task label for proof-cost JSON. The guide and
CLI help now give the command that creates the report. The correction review
had no findings. The packaging simplification passed the 27-test Nix suite at
`/nix/store/vsyxsqqxjln57s0li149h98xilq7726x-sqlite-verifier-test-theoremDependencies-1`.

The packaging review had no findings. Full source checks identified the missing
Lean build-category entries for the directly executed exporter and its fixtures.
Their exact paths are now registered in the existing direct-fixture category;
the correction review had no findings.

The verdict passed at
`/nix/store/pv8yv3gjwkbwli4bd5h3akpf50ysnrhi-sqlite-verifier-verdict`.
The scheduled check report passed at
`/nix/store/id752rh1ffdllb1v7dw9xszj4jbfyhy1-sqlite-verifier-scheduled-check-reports`.
All required completion commands passed: `just test-full`, `just verdict`,
`just test-nix` and `just test-scheduled-checks`. No semantic mutant table changed.

The full Nix report contains 1,368 passing tests across 14 suites, with no
failures, errors or skips:
`/nix/store/s6rzxwmnqyg68lrn79fmydjnlyqip7xx-sqlite-verifier-test-reports`.
Its surface suites passed 366 and 41 tests respectively. The workspace links
this report at `build/nix-tests-full`.

The full Nix run reached 96% of the existing 407-case surface suite without an
assertion failure, then hit that suite's 1,200-second limit. The same issue is
already fixed by the reviewed `tasks/surface-suite-split` branch. Merged its
`43a4c304` head, preserving both new suites in the suite-ownership assertion.
The split changes no test or timeout. Its restored review records are also
retained. The merge review had no findings.

The combined full check found an existing surface-build allowlist that omitted
the new report. Registered the report's three exact build references and added
an explicit check that the conformance runtime names no surface package. This
preserves ADR 0016 D2: standalone inspection is above the libraries, while the
model, translation and conformance layers stay below the surface. The correction
review had no findings, and the final full Nix run passed that check.
The completion-record review also had no findings. All review findings have
recorded outcomes, and the implementation is ready for the owner's review.
