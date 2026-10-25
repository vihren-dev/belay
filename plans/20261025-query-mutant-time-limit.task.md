# Keep the general mutant tests within their time limit

Created 2026-10-25. Status: DONE on 2026-10-25.
Audience: implementers and reviewers.
Progress: [status](20261025-query-mutant-time-limit.status.md).
Inspected base: PR #252, `296f3a57`.

## Present problem

The manual hosted CI run `40156468777` of PR #252 executed the general mutant
suite (`mutants`) on both platforms. On each platform,
`tests/conformance_query_mutants_test.py::test_every_query_mutant_changes_a_verdict`
failed with `Timeout (>300.0s) from pytest-timeout` (Linux 300 s at the limit,
macOS 319 s). The earlier test of the suite passed (228 s and 209 s). The
`--exitfirst` flag of #252 then ended the suite, so the later tests of the suite
did not run on the hosted runners. The logs are in the diagnostics workspace,
`build/agent-logs/ci252-manual-job-{linux,darwin}.log`.

The test is one measurement of all 16 query mutants (eight model files). A
focused local Nix run on this VM took 160.60 s. Each mutant suite now has its
own hosted job (`.github/workflows/ci.yml`), so the current factor is the
speed of a hosted runner: the same test took more than 300 s there, so the
hosted time is at least 1.9 times the local time. The timeouts give only this
lower bound, not a measured ratio. The local target of about 125 s below is
therefore a provisional splitting target; only the hosted run validates it.

The module docstring of `tests/conformance_query_mutants_test.py` records an
earlier, similar failure of the number and query-without-FROM mutants. Its
reason, two mutant suites at the same time on one hosted runner, is
historical, but its fix is the pattern for this task: that measurement was
split into measurements of at most 124 s alone. The new docstring text
corrects the historical reason where it describes the current layout.

## Required outcomes

- Every test of the `mutants` suite, and of the two other mutant suites, ends
  within its unchanged per-test limit of 300 s on a hosted runner, and the
  `mutants` suite within its unchanged suite limit.
- The query mutants are measured in two or more measurements, each a group of
  related mutants (for example by model file), so that each takes at most
  about 125 s alone in a focused local Nix run (a provisional target; the
  hosted run is the required validation). Each measurement is one test
  with a docstring that names its subject, as the existing number split does.
- Every mutant, target and guard is kept. No mutant is removed or weakened, no
  limit is increased, and no test is skipped or marked as allowed to fail.
- The module docstring tells the measured durations of the new measurements
  (in the style of its existing note on the number mutants).
- If another test of the three mutant suites is above about 125 s alone, split
  it in the same way under this task. Measure the tests that the hosted run
  did not reach (the `mutants` suite stopped after its second test).
- Production packages, native cases, corpora, judge claims, the lock and the
  oracle stay unchanged.

## Tests and acceptance

- Focused local Nix runs, by name (`-k`), of each new or changed measurement,
  with their durations. Never run the broad mutant suites locally.
- The existing suite inventory, routing and ownership checks pass.
- The part ends with independent review, `just test-full` and `just verdict`;
  the task ends with `just test-nix` and `just test-scheduled-checks`.
- After publication, the owner starts the manual CI run on the branch. The
  task is done when the hosted `mutants`, `tableMutants` and `functionMutants`
  jobs execute all their tests and pass on both platforms. A new hosted
  failure is repaired under this task when it is a time limit, and reported
  when it is a surviving mutant.

## Relevant code and constraints

`tests/mutant_sets.py` (`measure_set`: one base copy, then the mutant copies in
parallel), `conformance/query_mutants.py` (`MUTANTS`, `TARGETS`),
`tests/conformance_query_mutants_test.py` (the number split in
`number_mutant_table` is the pattern), `tests/nix_mutant_suites.json` and
`build-support/tests.nix` (suites and limits). The base copy builds almost
every module, so the time of a measurement grows with the number of distinct
mutated files that its mutant copies rebuild.
