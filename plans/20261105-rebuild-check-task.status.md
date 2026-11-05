# The guide's table rebuild adds a CHECK constraint: task status

Date: 2026-11-05. Status: in progress.
Audience: the implementation team.
Task: [The guide's table rebuild adds a CHECK constraint](20261105-rebuild-check-task.task.md).
Specification: the task file; the launch decision of the owner on 2026-11-05 (private product
repository, `launch-outlines/public-readme.md`).
Source baseline: `main` at 2b44247a (#313).

Relevant files: `packages/belay-sqlite-model/Belay/Sqlite/Model/CopyInsertFits.lean`;
`tests/surface/RebuildGuide.lean`, `RebuildCopyFacts.lean`, `RebuildSucceedsCopy.lean`,
`RebuildSucceedsSteps.lean`, `RebuildSucceedsFinish.lean`, `RebuildSucceeds.lean`,
`RebuildKeeps.lean` and its fixtures, `RebuildRefutation.lean`, `RebuildReplays.lean`;
`tests/surface_rebuild_test.py`; `docs/spec-proof-query-observation-targets.md`.

Tests of the task: `tests/surface_rebuild_test.py` (four tests), `tests/lean_packages_test.py`.

## Progress

- 2026-11-05: task specified.
