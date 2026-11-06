# Status: give each mutant suite only the Python modules and data that it reads (#330)

Created: 2026-11-06. Status: open.
Task: [20261106-narrow-mutant-inputs.task.md](20261106-narrow-mutant-inputs.task.md).
Issue: #330. Stacked on the #328 fix of [the CI bug task](20261106-ci-bug-fixes.task.md).

Sources: `build-support/tests.nix` (`mutantInputs`, `modelInputs`), `tests/nix_mutant_suites.json`,
`tests/nix_suites.json`, `tests/test_conformance_frontend.py` (`import_closure`),
`tests/test_nix_test_targets.py`.

## Progress

- 2026-11-06: task and status files.
- 2026-11-06: reviews of the task file: three R19 findings (shared harness files, the module
  count, what an import check can find), fixed by wording.
- 2026-11-06: `tests/nix_mutant_inputs.json` lists the modules of each suite (49 to 84);
  `build-support/tests.nix` gives each suite its list and the two Lean packages. The closure
  helpers moved to `tests/python_imports.py`. Tests run: `tests/test_mutant_suite_inputs.py`
  (fails with the old inputs), `tests/test_conformance_frontend.py`,
  `tests/test_nix_test_targets.py`, `tests/docs_test.py`. Smoke check: each declared module of
  each suite imports in the suite's Nix source tree (12 of 12 suites).
