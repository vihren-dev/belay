# Status: the table-rebuild example as a Lake project under `examples/`

Created 2026-11-13. Status: DONE (2026-11-13). Task: `20261113-examples-table-rebuild.task.md`.

Relevant files: `README.md`, `examples/table-rebuild/` (`TableRebuild.lean`, `FixedSucceeds.lean`,
`lakefile.toml`, `README.md`, the proof modules in `Proof/`), `tests/surface_rebuild_test.py`,
`tests/surface_support.py`, `build-support/tests.nix`, `tests/test_lean_categories.py`,
`docs/guide/agents.md`, `skills/belay/SKILL.md`.

## Progress

- 2026-11-13: task written. Tried the library's tactics on `fixed_keeps_sessions` in a project that
  requires Belay by path: `sql_auto` (all routes fail), `sql_commute` after `intro` (only
  `Migration.PreservesAt`), `#sql_check` with budget 500000 (`unknown`). The proof moves.
- 2026-11-13: the example project `examples/table-rebuild` (lakefile with Belay by path, `TableRebuild.lean`
  with the README's code, `FixedSucceeds.lean`, `README.md`) and the ten proof modules moved from
  `tests/surface/{Schema/Tests,Programs/Scripts}` to its folder `Proof`; `RebuildExample.lean` is replaced
  by the two example files. `fixture_file` also finds the example's files, the surface suites take the
  folder as an input, and `test_lean_categories` counts it as a direct fixture. The README test of
  `tests/surface_rebuild_test.py` now builds the project with Lake from the installed packages
  (`test_example_project_of_the_readme_builds_checks_and_proves_its_claims`). README, page for agents
  and skill name the new places. Tests: `tests/surface_rebuild_test.py`, `tests/test_lean_categories.py`,
  `tests/docs_test.py`; the Lake test needs the Nix runtime (in the development layout Lake fetches
  Plausible with git).
- 2026-11-13: `just test-full` passed (exit 0; the seven suites that the change touches ran, 1072
  tests, none failed), with `test_example_project_of_the_readme_builds_checks_and_proves_its_claims`
  in `surfaceS6` (45 s). DONE.
- 2026-11-13: rebased onto #400 (`fix/macos-suite-limit`, 6939aed7). `just dev-build` passed and
  `just test-full` passed on the rebased tree (exit 0; seven suites, 1072 tests, none failed), with
  `test_example_project_of_the_readme_builds_checks_and_proves_its_claims` in `surfaceS6`.
