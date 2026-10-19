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
