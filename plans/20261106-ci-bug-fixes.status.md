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
