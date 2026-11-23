# Status: pilot of one exact rule for each statement kind

Created 2026-11-23. Task: [20261123-statement-rule-pilot.task.md](20261123-statement-rule-pilot.task.md).
[Belay issue 468](https://github.com/vihren-dev/belay/issues/468).

## State

Started. The task file is written. No code is changed.

## Start revision

`b7854558` on `main` ("Reconstruct computed SQLite catalogs for
counterexample replay (#463)").

## Sources

- `packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Scripts/ScriptRun.lean`:
  `runScriptStepWith`, `ranScriptStep`, `runScriptStep`.
- `…/Programs/Scripts/ScriptRunContinued.lean`: `runScriptStep_continued_spec`.
- `…/Programs/Scripts/CreateTableStepLaws.lean`, `CreatedTables.lean`,
  `StepContinuesOk.lean`, `ResolvedStepGuards.lean`: the CREATE TABLE laws.
- `…/Programs/Scripts/PlainInsertStep.lean`, `PlainInsertEffect.lean`,
  `…/Schema/Writes/PlainInsertSuccess.lean`, `LiteralInsertFits.lean`,
  `StatementRun.lean`, `PlainCounts.lean`: the plain INSERT laws and
  definitions.
- `packages/belay/Belay/Sqlite/Programs/Scripts/SendStepRules.lean`,
  `SchemaStepRules.lean`, `PlainInsertStepRule.lean`,
  `…/Programs/Automation/SqlRunRules.lean`: the surface rules and the
  rule table of `sql_run`.

## Progress log

- 2026-11-23: wrote the task file and this file.
