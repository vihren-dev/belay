# Status: a readable counterexample from `#sql_check`

Created: 2026-11-05. Status: IN PROGRESS.
Task: [20261105-readable-counterexample.task.md](20261105-readable-counterexample.task.md).
Issue: #316.

Sources: `packages/belay/Belay/Sqlite/CheckDisplay.lean`, `CheckOperation.lean`,
`CheckReplay.lean`, `ReplayScript.lean`, `ReplayValues.lean`, `ReplayDatabaseSql.lean`,
`CounterexampleWitness.lean`; `Model/OutputTable.lean` (`textTable`).

## Progress

- 2026-11-05: task and status files.
- 2026-11-05: review of the task file: R19 must (a backslash in a text literal is kept by the
  shell's script input) fixed in the task file; the code keeps backslashes in literals.
- 2026-11-05: the readable counterexample. `CheckWitnessText.lean` (new) gives the tables and the
  environment; `CheckOperation` keeps them in `Outcome.witness`; `CheckReplay.scriptName` labels
  each report (`Replay.Report.label`); `CheckDisplay.describe` gives one block with one
  construction and one replay script (`.open :memory:` between replays); `Replay.textLiteral`
  spells UTF-8 text without NUL as a string literal. New fixture
  `tests/surface/CounterexampleReadable.lean` and test `tests/surface_check_readable_test.py`
  (suite `surfaceChecks`). Tests run for this commit: `surface_check_readable_test`,
  `surface_replay_test`, `surface_check_command_test`, `surface_automatic_test`,
  `surface_automatic_editor_test`, `surface_s6_check_editor_test`, `surface_s6_not_blocked_test`,
  `surface_s6_check_programs_test`.
- Finding: the claim of issue #316 is `unknown` with the default `sql.checkBudget` (100000), on
  main before this change too; the fixture sets 2000000. Not changed here.
