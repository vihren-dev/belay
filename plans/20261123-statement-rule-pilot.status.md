# Status: pilot of one exact rule for each statement kind

Created 2026-11-23. Task: [20261123-statement-rule-pilot.task.md](20261123-statement-rule-pilot.task.md).
[Belay issue 468](https://github.com/vihren-dev/belay/issues/468).

## State

In progress. The CREATE TABLE kind rule and the generic projections are in
the model. The plain INSERT rule, the surface bridge, `sql_run`, the tests and
the findings record are open.

## Start revision

`b7854558` on `main` ("Reconstruct computed SQLite catalogs for
counterexample replay (#463)").

## Sources

- `packages/belay-sqlite-model/Belay/Sqlite/Model/Programs/Scripts/ScriptRun.lean`:
  `runScriptStepWith`, `ranScriptStep`, `runScriptStep`.
- `…/Programs/Scripts/ScriptRunContinued.lean`: `runScriptStep_continued_spec`.
- `…/Programs/Scripts/CreateTableRule.lean`: the CREATE TABLE kind rule;
  `StepRuleProjections.lean`, `StepRuleAttr.lean`: the generic projections
  and the simp set of the kind rules; `CreatedTables.lean`,
  `ResolvedStepGuards.lean`: users of the rule and its condition.
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
- 2026-11-23: review `20261123T141236Z-52986bdc` of the task file gave 9
  "must" and 2 "should" findings. Ten are fixed in the task file: the
  retention test covers the surface laws, the ended case of INSERT
  names the three readiness checks, the new fixtures belong to the
  existing surface suites, and the end-of-task checks are restored.
  Finding 5 (module timing) is rejected with its reason in the record.
- 2026-11-23: review `20261123T141553Z-13640dbc` gave 3 "must" findings
  on the cases in which a plain INSERT ends the run and on the import
  limit. All three are fixed in the task file.
- 2026-11-23: review `20261123T141711Z-4f02a69d` gave 1 "must" and 1
  "should" finding on the same cases. Both are fixed in the task file.
- 2026-11-23: review `20261123T141827Z-1b4c4e51` gave no "must" finding
  and 1 "should" finding, which is fixed.
- 2026-11-23: baseline measurements (scc, statement lines, elaboration
  times) are in the scratch directory of the session.
- 2026-11-23: model: the simp set `step_rule` (`StepRuleAttr.lean`), the
  generic projections of a kind rule (`StepRuleProjections.lean`:
  `RunStep.Continuing`, `RunStep.of_rule`, `continued_of_rule`,
  `others_of_rule`, `ne_oneOf_of_rule`, `isError_of_rule`; `RunStep.continues`
  moved here), `Database.createTable`, `Connection.withDatabase` (moved from
  the surface), `Database.table_createTable_end`, and the CREATE TABLE kind
  rule `runScriptStep_createTable_eq` (`CreateTableRule.lean`).
  `CreateTableStepLaws.lean` (`runScriptStep_createTable`, `_frame`),
  `runScriptStep_createTable_ok` and `runScriptStep_createTable_empty` are
  deleted; TableKeeps, SchemaFailureLaws, CreatedTables,
  CreateSchemaSuccess, the surface `Sql.check_send_createTable` (its
  removal is planned for the commit of the surface bridge) and the fixture
  SchemaCreateExamples use the rule.
  Tests: `just dev-build`, `tests/surface_schema_script_test.py`,
  `tests/surface_s6_automation_test.py`,
  `tests/surface_assertion_examples_test.py`, the root-import test of
  `tests/test_model_package.py`. Two local runs fail for this machine, not
  for the change: the Nix model build of
  `test_installed_core_and_codec_consumer` exceeds its 120 s limit when the
  model is not cached, and the README example of `surface_rebuild_test.py`
  cannot clone `plausible` (no `git`). `just test-full` runs the README
  example and `just test-nix` runs the installed consumer test.
