# The guide's table rebuild makes the table STRICT: task status

Date: 2026-11-05. Status: DONE (2026-11-05), pull request open.
Audience: the implementation team.
Task: [The guide's table rebuild makes the table STRICT](20261105-rebuild-check-task.task.md).
Specification: the task file; the launch decision of the owner on 2026-11-05 (private product
repository, `launch-outlines/public-readme.md`).
Source baseline: `main` at 2b44247a (#313).

Relevant files: `packages/belay-sqlite-model/Belay/Sqlite/Model/CopyInsertFits.lean`;
`tests/surface/RebuildGuide.lean`, `RebuildCopyFacts.lean`, `RebuildSucceedsCopy.lean`,
`RebuildSucceedsSteps.lean`, `RebuildSucceedsFinish.lean`, `RebuildSucceeds.lean`,
`RebuildKeeps.lean` and its fixtures, `RebuildRefutation.lean`, `RebuildReplays.lean`;
`tests/surface_rebuild_test.py`; `docs/spec-proof-query-observation-targets.md`.

Tests of the task: `tests/surface_rebuild_test.py` (five tests), `tests/lean_packages_test.py`.

## Progress

- 2026-11-05: task specified for a CHECK constraint. The review found that SQLite 3.53.0 adds
  CHECK constraints in place too (`ADD CONSTRAINT ... CHECK`); the owner chose STRICT instead,
  and the task file was rewritten. The file name keeps its first slug.
- 2026-11-05: `InsertFits.copy` takes `typed` (every source row fits the STRICT types of the target) in
  place of `untyped`; `just dev-build` passes. The fixtures name the scripts `makeStrict`,
  `makeStrictWrong` and `makeStrictWrongEnforced`, create `customers_new` as a STRICT table, name the
  new table's definition `strictShape` (from `reachedAfter 3`) with its facts checked by the kernel, and
  state the premise `StrictRows` with `LiteralData.typesFit strictShape`. The replay `with-blob` replaces
  `without-name`; the expected refusal of native SQLite is `cannot store BLOB value in TEXT column`. Tests
  of the commit: `tests/surface_rebuild_test.py` and `tests/lean_packages_test.py`; their results count
  from the Nix checks only.
- 2026-11-05: commit a4c46bff (the STRICT rebuild). Review: one "should" finding (R9), the docstrings
  of `makeStrict` and `makeStrict_succeeds` said "not text" where the copy refuses only a cell that does
  not fit its STRICT type and NULL fits every type; fixed in commit 32a11075. Its review: one "should"
  finding (R19), this file cited local test results; removed.
- 2026-11-05: `just test-full` on 32a11075: the first run failed in
  `tests/surface_check_command_test.py::test_sql_check_reports_checked_outcomes` by its 240 s command
  timeout while `just test-nix` and two reviews ran on the same machine; the second run, alone, passed
  (all 16 report groups). `just test-nix`: 87 passed. `just test-scheduled-checks`: passed (the writers group).
- 2026-11-05: DONE. The pull request of the branch `rebuild-strict` is open on `main`.
