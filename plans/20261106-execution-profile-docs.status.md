# Status: a user document for execution profiles (#19, one slice)

Created: 2026-11-06. Status: open.
Task: [20261106-execution-profile-docs.task.md](20261106-execution-profile-docs.task.md).
Issue: #19. Stacked on the #332 fix.

Sources: `docs/execution-profile.md`, `docs/native-corpus-format.md`,
`docs/conformance-model.md`, `packages/belay-sqlite-model/Belay/Sqlite/Model/Resolution/Profile.lean`,
`packages/belay-sqlite-text/Belay/Sqlite/Grammar.lean`, `conformance/profile_scope.py`.

## Progress

- 2026-11-06: task and status files.
- 2026-11-06: review of the task file: two R19 findings (the model implements foreign keys and
  recursive triggers; the release is metadata), fixed by wording.
- 2026-11-06: `docs/execution-profile.md` is a user document: the `Profile` fields, the releases,
  the assumptions, double-quoted strings, storage and the measurement of an application's build.
  A run continues after a failed statement (`packages/belay/Belay/Sqlite/Run.lean`), so the old
  "stop on the first error" is gone. The recorder text moves to the section "Execution profiles"
  of `docs/native-corpus-format.md`; links in `docs/conformance-model.md`,
  `docs/conformance-format-v2.md` and `docs/upstream-pilot.md` point to it, and the stale list
  of implemented settings in `docs/conformance-format-v2.md` is corrected. Tests run:
  `python3 -m pytest tests/docs_test.py` (the new vocabulary test fails on the old document).
