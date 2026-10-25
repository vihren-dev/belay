# Keep the model suite within its time limits on hosted macOS

Created 2026-10-25. Amended 2026-10-25 with measurements, the target of 25 s and the model ownership. Status: DONE (the hosted macOS run is for the owner to check).
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
  times were about 2.1 to 2.4 times the hosted Linux times. The target is at
  most about 25 s locally for the slowest proof process, which gives at most
  about 60 s on hosted macOS at the measured rate; only the hosted run
  validates it. Batching cannot reach this target (see "Measurements"): the
  means is a cheaper kernel evaluation of the JSON and JSONB text encoding in
  the model, with every frozen prediction byte-identical. A model change of
  more than about 200 lines, or one that cannot reach the target, stops the
  task; then the owner decides between two fallbacks. The first fallback is a
  judge change that splits the case `jsonb-header-sizes` (new corpus version
  and new lock, two pull requests). The second fallback is a CPU-time limit in
  place of the 120 s wall-time limit of `kernel_check`. Neither fallback is
  part of this task without that decision.
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
- Native cases, corpora, judge claims, the lock and the oracle stay unchanged.
  Production packages stay unchanged except for the files in "Ownership".

## Measurements

Local Nix runs of the `model` suite (`max-jobs = 1`, `cores = 2`; 8 cores; load
average 4 to 5 from other agents, so each time is an upper bound).

| Part of the `model` suite | Time | Tests |
| --- | --- | --- |
| Whole suite | 840 s | 251 |
| `tests/conformance_query_coverage_test.py` | 576.5 s | 45 |
| `tests/conformance_generation_test.py` | 55.9 s | 12 |
| `tests/foreign_key_atoms_native_test.py` | 44.3 s | 35 |
| `tests/conformance_query_sources_test.py` | 31.8 s | 2 |
| `tests/conformance_model_test.py` | 29.8 s | 20 |
| All other files | 100.5 s | |

The coverage tests are 69 % of the suite. Their case modules up to
`authored_drops` (28 modules) take 296 s; the later 17 modules take 280 s.

The slowest Lean proof processes of the coverage tests are `authored_jsonb`
`Cases0.lean` (55.8 s), then `authored_numeric_functions` (22.8 s),
`authored_printf` (22.4 s), `authored_json_edits` (19.8 s),
`authored_text_functions` (19.5 s), `authored_date_functions` (18.2 s) and
`authored_pragmas` (16.1 s). All other processes take 14.4 s or less. With one case for
each process, `authored_jsonb` takes 50.5 s for the case `jsonb-header-sizes`
and 2.9 to 6.4 s for each other case. Hosted Linux took 51.5 s and 58.5 s for
the whole test. A batch of any size therefore cannot go below about 50 s for
this case, because one case is one proof (`decide +kernel` of
`checkCase fixture = true`).

The profile of the proof of `jsonb-header-sizes`: import 0.8 s, elaboration
0.8 s, kernel type checking 56.6 s. Single-expression variants of the case,
each as its own proof, with a string of 300 bytes unless the table says
otherwise:

| Expression | Time |
| --- | --- |
| `jsonb_array(1, ... 1)` with 12 elements | 1.8 s |
| `jsonb('"<100 bytes>"')` | 3.3 s |
| `jsonb('"<256 bytes>"')` | 8.1 s |
| `jsonb('"<300 bytes>"')` | 21.6 s |
| `length(jsonb('"<300 bytes>"'))` | 9.8 s |
| `jsonb_array('<300 bytes>')` | 11.4 s |
| `jsonb_array('<300 bytes>', '<300 bytes>')` | 44.0 s |

The time grows much faster than the string length. The cause is in the kernel
evaluation of the model, not in the test infrastructure.

## Tests and acceptance

- Focused local Nix runs of each changed test or suite, with their durations.
  Never run the mutant suites locally.
- The existing suite inventory, routing and ownership checks pass.
- After each model change: `just dev-build`, then `just dev-verdict`, and the
  53 prediction files equal the files of a baseline built from the commit
  before the change. The local time of the proof of `jsonb-header-sizes` is
  measured again.
- The part ends with independent review, `just test-full` and `just verdict`;
  the task ends with `just test-nix` and `just test-scheduled-checks`.
- After publication, the owner starts the manual CI run on the branch. The
  task is done when the hosted macOS and Linux `Check` jobs pass. A new hosted
  time-limit failure is repaired under this task.

## Ownership

This task may change the model files that read JSON text and write JSONB, and
the byte and string functions that they use: the folder
`packages/belay-sqlite-model/Belay/Sqlite/Model/Json/` and
`packages/belay-sqlite-model/Belay/Sqlite/Model/ByteText.lean`. No other task
changes these files now. A change must keep the semantics: every frozen
prediction (all 53 prediction files) stays byte-identical to a baseline built
from the commit before the change, the Lean proofs of the packages still build,
and a mutant test that targets a changed file passes (run it by name).

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
