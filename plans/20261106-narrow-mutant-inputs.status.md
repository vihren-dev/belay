# Status: give each mutant suite only the Python modules and data that it reads (#330)

Created: 2026-11-06. Status: open.
Task: [20261106-narrow-mutant-inputs.task.md](20261106-narrow-mutant-inputs.task.md).
Issue: #330. Stacked on the #328 fix of [the CI bug task](20261106-ci-bug-fixes.task.md).

Sources: `build-support/tests.nix` (`mutantInputs`, `modelInputs`), `tests/nix_mutant_suites.json`,
`tests/nix_suites.json`, `tests/test_conformance_frontend.py` (`import_closure`),
`tests/test_nix_test_targets.py`.

## Progress

- 2026-11-06: task and status files.
