# The guide's table rebuild makes the table STRICT: task status

Date: 2026-11-05. Status: in progress.
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
  `without-name`. Local: every fixture chain of `tests/surface_rebuild_test.py` compiles with the three
  logical axioms; native `sqlite3` 3.51.0 refuses the blob with `cannot store BLOB value in TEXT column
  customers_new.email (19)` and gives the expected rows. Tests of the commit: `tests/surface_rebuild_test.py`
  and `tests/lean_packages_test.py` on the Nix conformance runtime.
- 2026-11-05: commit a4c46bff (the STRICT rebuild). Local: the five rebuild tests and the package
  replay test pass. Review: one "should" finding (R9), the docstrings of `makeStrict` and
  `makeStrict_succeeds` said "not text" where the copy refuses only a cell that does not fit its
  STRICT type and NULL fits every type; fixed in the next commit. `just test-full` runs on a4c46bff.
