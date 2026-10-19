# Test harness visibility

Created 2026-10-19. Status: in progress.
Status file: [status](20261019-test-harness-visibility.status.md).
Related: [CI](../docs/ci.md), [build and test behavior](../build-support/README.md),
[ADR 0001](../docs/adr-0001-pytest-and-nix-ci.md) (Nix test caching and the 2026-09-29
simplification), [hosted model timeout](../reports/20261006-hosted-model-timeout/README.md).

## Motivation

The Linux check of pull request #161 (run 39239259061, attempt 2) failed after 30
minutes in `just package`. The log shows no test case, no Nix build line and no
pytest line between 11:36 and the kill at 12:06. The only diagnostic is
`"A descendant outside the process group kept the output pipes open"`. Every
recorded test passed. The reports show that the step that ran last was
`test-scheduled`, but the log cannot show this.

Five causes, found while reading that run:

1. `run_command` (`tests/runtime_support.py`) holds all output in memory until the
   command exits, so CI prints nothing while a phase runs.
2. On a timeout it replaces the partial output with that fixed sentence.
3. The justfile runs `timeout N nix-build ...`. GNU `timeout` without
   `--foreground` moves itself into a new process group, so the CI phase kill does
   not reach `timeout` or `nix-build`. They keep the pipes open.
4. Each Nix suite has a 1200-second limit (`suiteTimeoutSeconds` in
   `build-support/tests.nix`), but the recipes that build the suites stop
   `nix-build` after 900 seconds. The suite limit, which exists to name the suite
   that hangs, cannot fire.
5. `nix-build -A tests --out-link build/nix-tests-full` names the reports
   `build/nix-tests-full-2` ... `-13` in alphabetical order of the suites. The CI
   artifact also mixes reports of this run with reports that Nix reused from an
   earlier build, and nothing tells them apart.

## Outcome

1. **Live output.** While a CI phase runs, each line that its command writes
   appears in the Actions log when the command writes it: Nix build lines and
   pytest `-v` lines. The output of a phase is not printed twice.
2. **Partial output on timeout.** When a command times out, the result keeps all
   output read before the deadline, also when a process outside the killed
   process group keeps the pipes open. In that case the result says so, and
   `run_command` returns within a short, fixed grace period after the kill.
3. **Kill reaches nix-build.** Every justfile recipe that runs `nix-build` under
   `timeout` keeps it in the caller's process group (`timeout --foreground`), so a
   process-group kill by `run_command` stops it.
4. **Limits nest.** Each limit is shorter than the limit around it: per test (300 s)
   < per suite < each recipe or CI phase that builds suites with `nix-build`
   (including the Darwin bundle phase). A suite that hangs outside a test
   therefore fails with its own name.
5. **Reports named by suite.** The CI artifact holds one JUnit report per suite at
   a path that names the suite, for example `build/nix-tests-full/frozen/junit.xml`.
   `just test`, `just test-full` and `just test-scheduled` follow the same layout.
6. **Ran or reused.** After the checks phase, pass or fail, CI prints a summary to
   the log and to the job summary page: for each JUnit report, its tests,
   failures, time, and whether it ran in this job or was reused from an earlier
   build (with that build's date); and the ten slowest test cases that ran in this job.

## Tests

- `run_command` with streaming on: a child that writes lines with pauses between
  them; each line reaches the parent's stream before the child exits.
- `run_command` timeout with a grandchild that starts its own session and holds
  the pipes: the result has the output written before the deadline and the note,
  and the call returns in a few seconds, not when the grandchild exits.
- The existing timeout test (`tests/test_pytest_harness.py`) still passes: the group
  is killed and the partial output kept.
- CI orchestration tests (`tests/test_ci_checks.py`, `tests/test_ci_bundle_scheduling.py`)
  check that phases stream, that a timeout prints a short diagnostic without the
  streams again, and that the summary is written after a failed phase too.
- A justfile test: every `nix-build` recipe under `timeout` uses `--foreground`, and
  the recipes that build suites have a limit above the suite limit that Nix renders
  (`tests/test_nix_test_targets.py` renders the real suite commands).
- A Nix evaluation test: the report targets link exactly the suites of `tests`,
  `developmentTests` and `scheduledTests`, each under its own name;
  `tests/test_test_ownership.py` checks the recipes build them.
- Summary tests on small JUnit files: ran versus reused by timestamp, counts,
  time, the slowest-case list, a report without a timestamp, and an empty build folder.
- `just test-full` passes locally, and the pull request's Linux check passes with
  the new log and artifact layout.

## Implementation notes

- `run_command` is used by many tests with captured output. Streaming must be off
  unless the caller asks for it; only `tools/ci_checks.py` turns it on.
- `tests/runtime_support.py` is a common input of every Nix suite
  (`common` in `tests.nix`). Any change reruns all suites once. A new module that
  it imports must join `common`.
- Do not close a pipe from one thread while another thread reads it: a buffered
  reader's `close` waits for the reader's lock. Read both pipes in one thread
  (for example with `selectors`) so the deadline and the grace period stay simple.
- The owner removed the cleanup of descendants beyond the timed-out process
  group (ADR 0001, update 2026-09-29). Do not walk the process tree; keep
  `nix-build` in the group instead.
- `nix-build` builders run in the Nix daemon, so `--foreground`, which does not
  time out the command's children, loses nothing for `nix-build`. Recipes that run
  Python under `timeout` keep their behavior.
- The macOS `model` suite took 838.7 s on main (run 38787513511), so the suite
  limit cannot drop below 900 s. Raise the limits that build suites instead.
  The job limit (75 min) is the owner's and stays. The owner raised the checks phase
  limit from 1800 s to 3600 s on 2026-10-19, after the first CI run of this task showed
  that `just package` with a rerun of the mutant suite needs about 33 minutes.
- `nixpkgs.linkFarm` keeps its entries in `passthru.entries`, which a test can evaluate.
- `.github/workflows/ci.yml` is code-owned. The artifact path `build/nix-tests*/`
  already matches the new layout; avoid changing the workflow if possible.
- Old numbered out-links (`build/nix-tests-full-2` ...) stay in local checkouts as
  garbage-collector roots until someone deletes them.
