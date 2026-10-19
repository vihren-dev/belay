# Status: test harness visibility

Created 2026-10-19. Status: in progress.
Task file: [task](20261019-test-harness-visibility.task.md).

## Relevant files

- Command runner: `tests/runtime_support.py` (`run_command`), its tests in
  `tests/test_pytest_harness.py`.
- CI orchestration: `tools/ci_checks.py`, tests in `tests/test_ci_checks.py` and
  `tests/test_ci_bundle_scheduling.py`.
- Recipes: `justfile`; recipe tests in `tests/test_test_ownership.py`.
- Nix suites: `build-support/tests.nix` (`suiteTimeoutSeconds`),
  `build-support/default.nix` (`tests`, `developmentTests`, `scheduledTests`),
  `tests/test_nix_test_targets.py`.
- Documentation: `docs/ci.md`, `build-support/README.md`.

## Evidence

- Failed run: pull request #161, run 39239259061, attempt 2. Last report written
  11:52 (`installed.xml`); kill at 12:06 during `test-scheduled`.
- Last successful Linux run: 39251279911 (`tasks/claim-collations`), 16 minutes,
  1,386 cases, 15 of them reused from 2026-10-13.

## Progress

- 2026-10-19: task and status files written.
- 2026-10-19: outcomes 1 and 2. `run_command(echo=True)` streams through one
  selector loop; on a timeout it keeps the output read so far and, when the pipes
  stay open after the kill, stops after 5 seconds with a note. `ci_checks.py` streams
  every phase and prints a one-line timeout message. Stream tests are in
  `tests/test_command_streams.py` (review: keep `test_pytest_harness.py` < 200 lines).
- 2026-10-19: outcomes 3 and 4. Every justfile `nix-build` runs under
  `timeout --foreground`; the suite recipes use `suite_build_limit` (1500 s) and the
  Darwin bundle phase 1500 s, above the 1200-second suite limit.
  `tests/test_recipe_limits.py` checks both.
- 2026-10-19: outcome 5. `testReports`, `developmentTestReports` and
  `scheduledTestReports` (linkFarm) give `build/nix-tests-full/SUITE/junit.xml`.
  Local `just test-full` passed; the first attempt failed one atuin case
  (`migration-proof-checker` 30-second limit) at load average 27 from another
  session's mutant suite, and passed on the rerun.
- 2026-10-19: outcome 6. `tools/test_reports.py` prints the report summary after the
  checks phase, also on failure, and adds it to `GITHUB_STEP_SUMMARY`.
- Next: pull request; check the Linux job's log, artifact layout and summary page.
