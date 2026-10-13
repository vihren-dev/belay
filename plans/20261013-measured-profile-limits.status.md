# Status: measured profile limits, error phase and resolve mutants, step 2a of ADR 0008

Created 2026-10-13. Status: IN PROGRESS.
Task: [task](20261013-measured-profile-limits.task.md).
Specification: [ADR 0008](../docs/adr-0008-syntax-and-resolution-in-lean.md).
Previous step: [step 1b status](20261012-resolution-switch.status.md).

Relevant files: `conformance/native_connection.py`,
`conformance/execution_profile.py`, `conformance/native_trace.py`,
`conformance/native_statements.py`, `conformance/case_format.py`,
`conformance/model_cases.py`, `conformance/mutation_check.py`,
`VerifierConformance/Case.lean`, `VerifierConformance/Native.lean`,
`VerifierConformance/Json.lean`,
`packages/belay-sqlite/Belay/Sqlite/Resolution/Profile.lean`.

## Findings

- Survey, 2026-10-13, on `main` `6c9ec7a6`: the forced column limit is set at
  `native_connection.py:74` and read back at `:83`. No Lean code reads a
  recorded profile; `Case.lean` and `Predict.lean` use `Profile.documented`.
  The Python profile has no limits. The error phase is not recorded; both
  recorders raise one `NativeError` for prepare and step failures. The judge
  compares only the primary code, so comparing the phase in the judge is a
  locked change (step 2b). `mutation_check.py` mutates no resolution module.

## Progress

- 2026-10-13: task and status files created in the jj workspace `adr8-step1`,
  from `main` `6c9ec7a6`. The judge-claims pull request #101 (new `mustAgree`
  cases after step 1b) is open for owner approval.

## Remaining

- All outcome items of the task.
