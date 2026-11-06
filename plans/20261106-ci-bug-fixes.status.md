# Status: fix the CI bugs #333, #326, #329, #327 and #328

Created: 2026-11-06. Status: open.
Task: [20261106-ci-bug-fixes.task.md](20261106-ci-bug-fixes.task.md).
Issues: #333, #326, #329, #327, #328. Stacked on PR #324.

Sources: `build-support/tests.nix`, `.github/workflows/ci.yml`, `docs/ci.md`,
`conformance/resolve_mutants.py`, `tests/mutant_sets.py`, `tests/test_ci_workflow.py`,
`tests/test_nix_test_targets.py`, `tests/mutation_edits_test.py`.

## Progress

- 2026-11-06: task and status files.
- 2026-11-06: reviews of the task file: one R19 must (an archive of an earlier passed run of the
  same tree can be published after a failed check) and one should, both fixed by exact wording.
- 2026-11-06: #333: `__darwinAllowLocalNetworking` on the `observability` suite. The Linux
  derivation keeps its path; only the macOS one changes. Tests run:
  `tests/test_nix_test_targets.py` (new test evaluates the suites for macOS).
- 2026-11-06: #326: the tree part of the cache key is `git ls-files --stage` without `plans/` and
  `reviews/`, hashed with `git hash-object`, in a step directly after the checkout of each of the
  three jobs; the publisher warns when it finds no saved store. Tests run:
  `tests/test_ci_workflow.py`, `tests/test_ci_scope.py`, `tests/docs_test.py`, actionlint.
- 2026-11-06: #326 reviews: two shoulds (no test of the publisher's warning; test file over 200
  lines), fixed: a test of the warning, the cache-key tests in `tests/test_ci_cache_key.py` and
  the shared helper `tests/ci_workflow_text.py`.
- 2026-11-06: #329: `conformance.mutant_builds.built_base` copies and builds the base once per
  process; `measure` still classifies its cases with the unchanged model first. The review asked
  for files under 200 lines, so the Lake builds moved to `conformance/mutant_builds.py` (a new
  input of the Nix suites). Tests run: `tests/mutation_edits_test.py` (new test: two measurements,
  one base build), and `tests/conformance_function_mutants_test.py -k "printf or aggregate"` in one
  process: the second test did not build the base.
- 2026-11-06: #327: `publish-nix-store` runs unless the run was cancelled; each platform uploads
  only on an exact hit of its saved store, which cache-nix-action saves only after a passed check
  job (`post-if: success()` in its pinned `action.yml`). Tests run: `tests/test_ci_workflow.py`,
  `tests/test_ci_cache_key.py`, `tests/test_ci_scope.py`, `tests/docs_test.py`, actionlint.
- 2026-11-06: #328: the `mutants` job evaluates the suite derivation with `nix-instantiate` and
  restores the report of an accepted run under `mutant-report-v1-SYSTEM-DERIVATION`
  (`actions/cache` v6.1.0, pinned); a hit skips the store restore and the run, a passed eligible
  run saves its report. The mutants-job tests moved to `tests/test_ci_mutants_workflow.py`.
  Tests run: the three workflow test files, `tests/test_ci_scope.py`, `tests/docs_test.py`,
  actionlint, and the derivation step's command locally.
