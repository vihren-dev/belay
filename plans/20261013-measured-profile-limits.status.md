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

- 2026-10-13: commit `d7eb0b03`: native connections keep the build's limits;
  `conformance/native_limits.py` measures and lowers them; profile format 3
  records them, and an older profile takes them from its compile options;
  `NativeError.phase`. Finding: SQLite cannot read its schema table with a column
  limit below 5, so the recorder refuses lower values. Review
  `20261013T024942Z-d7eb0b03`: four should findings, fixed in `cc7c9cf0`; its
  review has no findings.
- 2026-10-13: case version 4: the case carries the measured profile and each
  native error's phase; Lean resolves under the recorded profile and compares the
  phase when the record has it (cases from frozen corpus records have none, until
  step 2b). The five model cases and the injected-corruption regression are
  regenerated with `just conformance --prove` and `regressions.freeze` (new
  `caseSha256` 8477dc93...). `tests/conformance_phase_test.py` checks both phases.
- 2026-10-13: commit `2dd26f96` (case version 4). Review
  `20261013T030157Z-2dd26f96`: two should findings; the error message is fixed in
  `a09734dc`, and the missing lowered-limit test comes with the next commit.
- 2026-10-13: nine authored model cases: ASCII-only folding (an ASCII case
  variant collides, a non-ASCII variant does not), a table with an index's name,
  COMMIT and ROLLBACK without a transaction, BEGIN-ADD-ROLLBACK, and three cases
  under a column limit lowered to 5 (reached, exceeded, limit before duplicate).
  All 14 cases agree and the 13 small ones are kernel-proved. The generation
  test's column boundary uses a lowered limit instead of 2,000 columns. The
  model suite takes about 165 s instead of 88 s in one local run.
- 2026-10-13: commit `1c575626` (authored cases); review: no findings.
- 2026-10-13: resolve mutants (`conformance/resolve_mutants.py`, Nix suite
  `mutants`): 11 mutants, each built as a changed copy of the two Lean packages
  and killed by a model case (about 19 s in the sandbox). Finding: a copy of
  single definitions in a private namespace, as `mutation_check.py` does, cannot
  mutate resolution, because dot notation still calls the originals. Finding:
  `VerifierConformance/Outputs.lean` imported all of `Belay.Sqlite`, so the
  closure of `Case` contained the specification proofs, which a mutant breaks;
  its imports are now the model modules it uses. Two cases added for the
  mutants (a `CHARINT` unique key, an `INTEGER PRIMARY KEY DESC`), and the
  non-ASCII neighbor now uses an uppercase non-ASCII name. 16 cases in all.

## Remaining

- All outcome items of the task.
