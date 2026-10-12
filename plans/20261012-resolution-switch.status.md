# Status: switch the verifier to Lean resolution, step 1b of ADR 0008

Created 2026-10-12. Status: IN PROGRESS.
Task: [task](20261012-resolution-switch.task.md).
Specification: [ADR 0008](../docs/adr-0008-syntax-and-resolution-in-lean.md).
Previous step: [step 1a status](20261010-syntax-resolution-core.status.md).

Relevant files: `belay/sqlite/`, `migration_check/`,
`packages/belay-sqlite/Belay/Sqlite/`, `SqliteVerifier/`, `GateCore.lean`,
`ProofChecker.lean`, `BundleChecker.lean`, `VerifierConformance/`,
`examples/`, `tests/`.

## Findings

- Survey, 2026-10-12, on `main` `5feb549e`: about 4,000 lines of Lean outside
  `Resolution/` use the old model, in the core package, `SqliteVerifier/`, the
  gate, the harness and the examples (784 lines). About 115 files mention
  `Schema`.
- The `.olean` gate trusts the compiled `SqlInputs` from the Python emitter.
  The bundle checker builds `nextSchema`, `script` and `profile` from the
  structural record and trusts the record's `nextSchema`.

## Progress

- 2026-10-12: task and status files created in the jj workspace `adr8-step1`,
  from `main` `5feb549e`.

## Remaining

- All outcome items of the task.
