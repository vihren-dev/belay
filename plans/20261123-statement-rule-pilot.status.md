# Status: pilot of one exact rule for each statement kind

Created 2026-11-23. Task: [20261123-statement-rule-pilot.task.md](20261123-statement-rule-pilot.task.md).
[Belay issue 468](https://github.com/vihren-dev/belay/issues/468).

## State

In progress. The CREATE TABLE and plain INSERT kind rules, the generic
projections, the surface bridge and the path of `sql_run` through the kind
rules are done, and the replaced laws are deleted. The no-capability-loss
test, the client-claims test and the findings record are open.

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
- `…/Programs/Scripts/PlainInsertRule.lean`: the plain INSERT kind rule;
  `…/Schema/Writes/PlainInsertSuccess.lean`, `PlainWriteFrame.lean`,
  `LiteralInsertFits.lean`, `StatementRun.lean`, `PlainCounts.lean`: the
  data lemmas and definitions of plain INSERT.
- `packages/belay/Belay/Sqlite/Programs/Scripts/KindRuleSend.lean`: the
  surface bridge `Sql.check_send_of_rule`; `SendStepRules.lean`,
  `SchemaStepRules.lean`: the remaining surface step rules;
  `…/Programs/Automation/SqlRunKindRules.lean`, `SqlRun.lean`,
  `SqlRunRules.lean`, `SqlRunGoals.lean`: `sql_run` and its rule table.

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
- 2026-11-23: reviews `20261123T150247Z-c86380e4` (4 must, 5 should),
  `20261123T150746Z-657e7308` (1 must, 1 should) and
  `20261123T151159Z-dc483d3a` (1 should): all fixed in two `refactor:`
  commits and in the next commit.
- 2026-11-23: model: the plain INSERT kind rule
  `runScriptStep_plainInsert_eq` (`PlainInsertRule.lean`), the data lemmas
  `insertOutcome_of_fits` and `insertReady_of_fits` (they replace
  `runStatement_insert_ok`, whose only caller was
  `runScriptStep_insert_ok`), and `Connection.afterError_failed`.
  This revision only rewrites the proof of `runScriptStep_insert_ok` with
  the rule; the deletion of the replaced INSERT laws and their surface
  callers is planned.
  Tests: `just dev-build`, `tests/surface_schema_script_test.py`,
  `tests/surface_s6_automation_test.py`,
  `tests/surface_assertion_examples_test.py`.
- 2026-11-23: review `20261123T152239Z-2a4b78b2` gave 7 "must" findings,
  all fixed in a `refactor:` commit: `runScriptStep_insert_ok` and
  `PlainInsertStep.lean` are deleted, and the fixture PlainInsertStepCases
  (`two_rows`) rewrites with the set `step_rule`; the docstrings of the
  data lemmas, the rule and `Connection.afterError_failed` say exactly
  what the formulas say. Tests: `just dev-build`,
  `tests/surface_schema_script_test.py`, the root-import test of
  `tests/test_model_package.py`.
- 2026-11-23: surface: the bridge `Sql.check_send_of_rule` with
  `Sql.SendReached`, `Sql.sendReached_single` and
  `Model.RunStep.continuing_ite` (`KindRuleSend.lean`); the model
  projection `RunStep.continues_of_rule`. `sql_run` applies the rules of the
  simp set `step_rule` through the bridge (`SqlRunKindRules.lean`) and
  keeps no `sendRule` entry for CREATE TABLE and INSERT. Deleted: the model
  `Programs/Scripts/PlainInsertEffect.lean` (`plainInsert_database`,
  `runScriptStep_insert_ne_oneOf`), the surface `PlainInsertStepRule.lean`
  (`Sql.check_send_plainInsert`), `Sql.ifOk_send_plainInsert` and
  `Sql.check_send_createTable`; `Reasoning/PlainInsertEffect.lean` is now
  `SendSingleStep.lean`. Changed callers: the fixtures SchemaRuleExamples,
  SignupInvariantClaims, GlobalSignupInvariant, S6AutoSignup,
  AddCustomerQueries, AddCustomerClaims, S6AutoAddCustomer and
  CustomerInsertSite (same claims, new proofs). Tests: `just dev-build`,
  `tests/surface_s6_automation_test.py`, `tests/surface_schema_script_test.py`,
  `tests/surface_assertion_examples_test.py`, `tests/surface_rebuild_test.py`
  (the README example needs `git`, which `just test-full` has), the
  root-import test of `tests/test_model_package.py`.
- 2026-11-23: review `20261123T161058Z-83cfffec` gave 6 "must" and 4
  "should" findings, all fixed in a `refactor:` commit: `sql_run` applies
  the bridge, the rules and their cases by tags instead of named holes, so
  one program can send many statements of one kind; a hint whose rewrite
  leaves a premise open selects no case; a case with a choice output stays
  unchanged; the guards of the step (`step_guards_hold`) close the premise
  `modeled` of CREATE TABLE on an abstract valid database;
  `RunStep.continuing_ite` moved to the model. New fixture
  `S6AutoKindRuleCases`; SchemaRuleExamples also proves the abstract CREATE
  TABLE claim with `sql_run [found]`. Tests: `just dev-build`,
  `tests/surface_s6_automation_test.py`, `tests/surface_schema_script_test.py`,
  `tests/surface_assertion_examples_test.py`, `tests/surface_rebuild_test.py`
  (without the README example), `tests/test_source_identity_derivations.py`.
- 2026-11-23: review `20261123T162716Z-79b29efc` gave 3 "must" and 1
  "should" finding, all fixed in a `refactor:` commit: `sql_run` finds the
  resolution premise of a kind rule by its type, and keeps every other
  unassigned premise of the rule as a goal; the docstring of
  `RunStep.continuing_ite` no longer describes the tactic. The fixture
  `S6AutoKindRuleCases` adds a kind rule with renamed premises. Tests:
  `just dev-build`, `tests/surface_s6_automation_test.py`,
  `tests/surface_schema_script_test.py`, `tests/surface_assertion_examples_test.py`,
  `tests/surface_rebuild_test.py` (without the README example).
