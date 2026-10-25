# Keep the model suite within its time limits on hosted macOS

Created 2026-10-25. Status: OPEN.
Audience: implementers and reviewers.
Progress: [status](20261025-macos-model-suite-limit.status.md).
Inspected base: PR #254, `e3baff02`.

## Present problem

The macOS `Check` job failed in the `model` Nix suite in both manual hosted CI
runs of the current stack. The Linux `Check` job passed in both runs.

| Run | Branch | macOS `model` result |
| --- | --- | --- |
| `40156468777` | `tasks/mutant-failure-diagnostics` (#252) | 1 failed, 250 passed in 1160 s; `authored_jsonb` proof batch `Cases0.lean` timed out after 120 s |
| `40174999810` | `tasks/query-mutant-time-limit` (#253) | exit 124: the suite limit of 1200 s ended the suite while it ran `authored_jsonb` |

The logs are in this workspace: `build/agent-logs/ci252-manual-check-darwin.log`,
`ci253-manual-check-darwin.log`, and the Linux peers
`ci40156468777-check-linux.log` and `ci40174999810-check-linux.log`.

Two limits fail:

- **Per-process limit.** `conformance/model_check.py` `kernel_check` gives each
  Lean proof process 120 s. `prove_all` checks `PROOF_BATCH` (8) cases per
  process. The first `authored_jsonb` batch took more than 120 s on hosted
  macOS. The whole `authored_jsonb` test took 121.6 s on macOS and 51.5 s and
  58.5 s on hosted Linux. The next slowest coverage test took 39 s on macOS.
- **Suite limit.** `build-support/tests.nix` gives each suite that is not a
  mutant suite 1200 s (`suiteTimeoutSeconds`; mutant suites have 2700 s). Its comment says that each test has its own limit
  and that the suite limit only guards against a hang outside a test. The
  hosted macOS `model` suite (28 test files, 251 tests) now takes about
  1160 s or more, so the suite limit binds. Hosted Linux took 714 s and 887 s.

The hosted macOS `Check` job runs on manual runs, scheduled runs and pushes to
`main`; PR runs skip it. The scheduled `main` runs pass, so the stack, not
`main`, makes the suite too slow. Two earlier fixes of hosted suite time are
recorded: `reports/20261006-hosted-model-timeout/README.md` raised the model
deadline from 420 to 600 s, and `plans/20261007-ci-suite-split.status.md`
split the CI suites by their dependencies. This task keeps the limits and
splits the work.

## Required outcomes

- Every Lean proof process of the coverage tests ends well within its
  unchanged 120 s limit on hosted macOS. Measure locally; the hosted macOS
  times were about 2.1 to 2.4 times the hosted Linux times. A provisional local
  target is at most about 40 s for the slowest proof process; only the hosted
  run validates it.
- The `model` suite, and each suite split from it, ends within the unchanged
  suite limit of 1200 s on hosted macOS with a clear margin. A provisional
  target: each resulting suite takes at most about 60 % of the local Nix test
  time of the current `model` suite, which gives about 700 s on hosted macOS
  at the measured rate. State the measured local times; only the hosted run
  validates them.
- Every test, case, proof and axiom audit is kept. No limit is increased, and
  no test is skipped, deselected or marked as allowed to fail.
- A new suite, if any, is listed in `tests/nix_suites.json`, built by
  `build-support/tests.nix` and reported by `just test-full` like the existing
  suites, and the suite inventory and routing checks cover it.
- The docstrings and comments that describe the changed batch size or suite
  layout tell the measured durations.
- Production packages, native cases, corpora, judge claims, the lock and the
  oracle stay unchanged.

## Tests and acceptance

- Focused local Nix runs of each changed test or suite, with their durations.
  Never run the mutant suites locally.
- The existing suite inventory, routing and ownership checks pass.
- The part ends with independent review, `just test-full` and `just verdict`;
  the task ends with `just test-nix` and `just test-scheduled-checks`.
- After publication, the owner starts the manual CI run on the branch. The
  task is done when the hosted macOS and Linux `Check` jobs pass. A new hosted
  time-limit failure is repaired under this task.

## Relevant code and constraints

`conformance/model_check.py` (`PROOF_BATCH`, `prove_all`, `prove_batch`,
`kernel_check`), `tests/conformance_query_coverage_test.py` (one test per
authored case module in `CASE_SETS`), `conformance/authored_jsonb.py`,
`tests/nix_suites.json`, `build-support/tests.nix` (`suite`,
`suiteTimeoutSeconds`, the `model`, `frozen` and `harness` suites and their
shared `modelInputs`). `prove_all` runs its batches in parallel with
`os.cpu_count()` workers, and Nix runs suites in parallel, so a smaller batch
adds Lean start-up work and competes with other suites for the same cores. The
hosted macOS runner has fewer cores than this VM.
