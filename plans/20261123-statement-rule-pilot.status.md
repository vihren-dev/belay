# Status: pilot of one exact rule for each statement kind

Created 2026-11-23. Task: [20261123-statement-rule-pilot.task.md](20261123-statement-rule-pilot.task.md).
[Belay issue 468](https://github.com/vihren-dev/belay/issues/468).

## State

In progress. The CREATE TABLE and plain INSERT kind rules, the generic
projections, the surface bridge, the path of `sql_run` through the kind
rules, the no-capability-loss test and the client-claims test are done, and
the replaced laws are deleted. The findings record
(`docs/records/statement-rule-pilot-findings.md`) is written.

The work stopped for the owner after four review rounds in a row with
new "must" findings on the findings record. The owner decided on
2026-11-23 to continue the review loop and to add case laws of plain
INSERT; the task file has a section for them.

The case laws of plain INSERT and their data facts are in the model
(`PlainInsertCases.lean`, `PlainInsertFailure.lean`), and the two INSERT
claims of the client-claims test use them.

The owner decided on 2026-11-23 to add a third form, a case type of
plain INSERT, before the end checks; the task file has the section
"Case type of plain INSERT".

Open:

- The findings record for the case type. The case type, its part for
  all statement kinds (`StepCase.lean`, `PlainInsertCase.lean`) and the
  second client test (`ItemInsertCaseClaims.lean`) are done.
- The open findings of review `20261123T174042Z-90ccc457` on the
  findings record, and the measurements of the record after the import
  fix and the case laws.

Checks: `just test-full` passes on the commit of the import fix, and
`just verdict` gives the same result as the start revision (see the
progress log). Both run again after the case laws. `just test-nix` and
`just test-scheduled-checks` have not run.

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
  `PlainInsertCases.lean`: its case laws `runScriptStep_insert_ok` and
  `runScriptStep_insert_failed`; `…/Schema/Writes/PlainInsertFailure.lean`:
  the data facts of a failed INSERT;
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
- 2026-11-23: review `20261123T163512Z-0a7adb4f` gave 1 "must" and 1
  "should" finding, both fixed in a `refactor:` commit: `sql_run` unfolds
  reducible definitions around a premise before it looks for the resolution
  equation, and the renamed rule of `S6AutoKindRuleCases` states its
  resolution premise with a reducible name. Tests: `just dev-build`,
  `tests/surface_s6_automation_test.py`.
- 2026-11-23: tests: the fixtures ReplacedStepLaws and ReplacedSendLaws
  prove the statement of each deleted model and surface law from the laws
  that remain (no capability loss). The fixtures ItemInsertSite,
  ItemInsertOutcomes and ItemInsertClaims prove the four client claims on
  the table `items` (INTEGER PRIMARY KEY alias): the three INSERT claims
  on arbitrary valid rows, and CREATE TABLE then INSERT on a valid
  database with an empty catalog;
  no proof names `runScriptStep`, `runScriptStepWith`, `resolveStatement`
  or `SqlState.statementRun`. `sql_run` gives the kind rule to the open
  goal `modeled` as the hypothesis `rule`. The five fixtures are roots of
  the suite `surfaceS6` and run in two new tests of
  `tests/surface_schema_script_test.py`. Review
  `20261123T163841Z-b5173e63` gave 1 "should" finding, fixed here. Tests:
  `just dev-build`, `tests/surface_schema_script_test.py`,
  `tests/surface_s6_automation_test.py`,
  `tests/surface_assertion_examples_test.py`,
  `tests/test_source_identity_derivations.py`.
- 2026-11-23: review `20261123T171431Z-94c3fa5e` gave 3 "should"
  findings on the words of the status file, of a test docstring and of
  the restated `Sql.ifOk_send_plainInsert`; all fixed in a `refactor:`
  commit. Tests: `tests/surface_schema_script_test.py`.
- 2026-11-23: review `20261123T171553Z-0a90bb7d` gave 1 "should" finding
  on the words of the restated `Sql.ifOk_send_plainInsert`; fixed in a
  `refactor:` commit. Tests: `tests/surface_schema_script_test.py`.
- 2026-11-23: review `20261123T171646Z-7b27fa70` gave 1 "should" finding
  on the length of a sentence in the same docstring; fixed in a
  `refactor:` commit. Tests: `tests/surface_schema_script_test.py`.
- 2026-11-23: review `20261123T171736Z-0bb29f50` gave 1 "should" finding
  on the first condition of the same docstring; fixed in a `refactor:`
  commit. Tests: `tests/surface_schema_script_test.py`.
- 2026-11-23: review `20261123T171825Z-f71a4164` gave 1 "should" finding
  on the length of a list item in the same docstring; fixed in a
  `refactor:` commit. Tests: `tests/surface_schema_script_test.py`.
- 2026-11-23: review `20261123T171913Z-a922ed7f` gave 1 "should" finding
  on the same list item (the old rows stay, the new rows follow); fixed
  in a `refactor:` commit. Tests: `tests/surface_schema_script_test.py`.
- 2026-11-23: the findings record
  `docs/records/statement-rule-pilot-findings.md`: code lines before and
  after by package and by origin, changed callers, statement lines of
  the replaced laws and their replacements, elaboration times, lost facts
  (none), findings and the estimate for the next kind. No code changes;
  no tests.
- 2026-11-23: review `20261123T172548Z-ce164ea8` of the findings record
  gave 7 "must" and 5 "should" findings, all fixed in a `refactor:`
  commit: per-package rows, the `SqlRunRules` lines charged to their
  kinds, caller lines apart from law lines, four changed `sql_run`
  proofs, corrected statement counts (125 before) with the real
  derivations, the `StepRuleAttr` timing, `sql_run [rfl]` on a concrete
  CREATE TABLE, the split of the client test and three CREATE TABLE
  review rounds. No code changes; no tests.
- 2026-11-23: review `20261123T173202Z-0cbedccd` gave 6 "must" and 2
  "should" findings on the record, all fixed in a `refactor:` commit:
  the moved `RunStep.continues` counts as zero, changed callers are
  counted as declarations, the new `sql_run` example and the law lines
  are apart from the caller lines, and the statement table counts only
  the new and restated theorems that each derivation uses (64 lines).
  No code changes; no tests.
- 2026-11-23: review `20261123T173547Z-e870248f` gave 4 "must" and 1
  "should" findings on the record, all fixed in a `refactor:` commit:
  both sides of the move of `Connection.withDatabase` count for CREATE
  TABLE, callers are counted by declaration lines, `sendRule` is the one
  caller in `sql_run`, and the statement table lists the kept theorems
  with their lines. This is the third review round in a row with "must"
  findings, all on the findings record. No code changes; no tests.
- 2026-11-23: review `20261123T174042Z-90ccc457` gave 1 "must" and 1
  "should" finding on the record: the import of `PlainInsertRule` in
  `SqlRunKindRules` and a one-line change in `hintedKinds` are counted
  as "once" but are specific to the pilot kinds, and the record calls
  two module docstrings references to a deleted law. Both are open. This
  is the fourth review round in a row with new "must" findings, so the
  work stops here and goes to the owner, as the task file and
  `CLAUDE.md` require.
- 2026-11-23: `just verdict` gave a verdict (exit 0). `just test-full`
  failed in one test:
  `tests/surface_layers_test.py::test_imports_are_own_modules_model_roots_and_lean[surface]`.
  `KindRuleSend.lean` and `SqlRunKindRules.lean` imported three inner
  modules of the model, which the surface must not import. The three
  imports were not needed and are removed. Tests after the fix:
  `just dev-build`, `tests/surface_layers_test.py`,
  `tests/surface_s6_automation_test.py`. This commit is not reviewed yet:
  the review loop waits for the owner after the stop.
- 2026-11-23: after the import fix, `just test-full` passes (exit 0).
  `just verdict` on the start revision `b7854558` and on the pilot
  (commit `24c5b8f8`, before the import fix, which changes no model
  file) gives the same `counts.json` and the same `report.json`.
  Open: the review of the import fix, the two open findings on the
  findings record, `just test-nix` and `just test-scheduled-checks`.
- 2026-11-23: the owner decided to continue the review loop and to add
  case laws of plain INSERT. The task file has the new section "Case
  laws of plain INSERT"; `runScriptStep_insert_ok` leaves the list of
  replaced laws, because its statement is the success law. Review
  `20261123T191311Z-67a9dc4b` of the import fix gave 1 "must" finding
  (the State section of this file, fixed here) and 1 "should" finding
  (the findings record does not count the three removed import lines).
  The "should" finding is deferred until the record is measured again
  after the case laws.
- 2026-11-23: review `20261123T191422Z-2e2d367c` of the task-file change
  gave 3 "must" findings and 1 "should" finding. Fixed: the case laws
  state the clock and counter premises as the kind rule does; the
  success law names the database of `Database.setRows` and says what it
  does not promise; the open work names the retention-test change; this
  log says that the import-line finding is deferred.
- 2026-11-23: review `20261123T191714Z-d2bebd76` gave 1 "must" finding:
  the acceptance text of the INSERT kind rule promised stored rows for
  each success. Fixed: it names `Database.setRows` and its condition.
- 2026-11-23: the case laws of plain INSERT. `PlainInsertCases.lean` has
  the success law `runScriptStep_insert_ok`, with the statement of the
  law of that name at the start revision, and the failure law
  `runScriptStep_insert_failed`. Both are proved from
  `runScriptStep_plainInsert_eq`. `PlainInsertFailure.lean` has the data
  facts: the counts of a failed INSERT (0 changed rows, no total), a
  repeated rowid fails `LiteralData.rowidsDistinct`, and rows without an
  alias mismatch whose result breaks a constraint or repeats a rowid give
  a constraint violation with the database before. The model root
  imports the case laws, and `lakefile.toml` lists both modules. Tests:
  `just dev-build`, `tests/test_model_package.py` (root imports),
  `tests/surface_layers_test.py`, `tests/surface_schema_script_test.py`.
- 2026-11-23: review `20261123T192802Z-7dbeba93` of the case laws gave 3
  "must" findings and 1 "should" finding, all on docstrings, all fixed in
  a `refactor:` commit: the failure law says that a failed outcome
  carries the database before; the constraint-violation fact says that
  it checks the given result table; the model module docstring no longer
  describes the surface bridge; the module docstring of the data facts
  says how a caller uses them. Tests: `just dev-build`.
- 2026-11-23: review `20261123T193002Z-828230ef` gave 1 "must" finding:
  the failure law binds the database of the error outcome as `reached`,
  so the docstring now says that it is the database before and that the
  counts do not use it. Tests: `just dev-build`.
- 2026-11-23: the retention test no longer restates
  `runScriptStep_insert_ok`, because the model has it again as the
  success case law, with the statement of the start revision.
  `ReplacedStepLaws.lean` proves six deleted model laws, and
  `tests/surface_schema_script_test.py` expects six axiom reports. The
  "should" finding of review `20261123T193144Z-ba44164b` (a long
  sentence in the failure-law docstring) is fixed here. Tests:
  `just dev-build`, `tests/surface_schema_script_test.py`.
- 2026-11-23: the failure law `runScriptStep_insert_failed` takes an
  outcome with the database before, not an arbitrary database, and it
  passes that database in the error pair of the counts, which leaves
  the counts unchanged. Each error outcome of `insertOutcome` has the
  database before (`insertOutcome_error`), so the law covers the same
  cases. With an arbitrary database, Lean cannot infer that database
  from the goal of the client. Tests:
  `just dev-build`, `tests/surface_schema_script_test.py`.
- 2026-11-23: the two INSERT claims of the client-claims test use the
  case laws through `Sql.check_send_of_rule` and name no kind rule:
  `insert_new_check` uses `runScriptStep_insert_ok`, and
  `insert_taken_check` uses `runScriptStep_insert_failed` with
  `LiteralData.insertCounts_error_changes`. `items_taken_outcome` is
  proved with `insertOutcome_constraintViolation` and
  `LiteralData.rowidsDistinct_eq_false_of_repeated`, and the site fact
  `items_aliases` is deleted. `create_then_insert` uses
  `insert_new_check`, and `insert_keeps_names` keeps its `sql_run`
  proof. `sql_run` does not use the case laws: tagging them `step_rule`
  would let `sql_run` choose a case law before the kind rule and leave
  its premises open. Review `20261123T194046Z-08cc0e45`: the "must"
  finding on a test of the failure law is fixed here; the status text
  and the docstring lists of the two laws are fixed here. Tests:
  `just dev-build`, `tests/surface_schema_script_test.py`,
  `tests/surface_s6_automation_test.py`, `tests/surface_layers_test.py`.
- 2026-11-23: review `20261123T194335Z-9b5b9759` gave 1 "must" finding
  (the State section listed the client claims as open) and 1 "should"
  finding (a long sentence in the docstring of the client-claims test);
  both fixed in a `refactor:` commit. Tests:
  `tests/surface_schema_script_test.py`.
- 2026-11-23: the owner decided to add a third form, a case type of
  plain INSERT. The task file has the new section "Case type of plain
  INSERT", three new bullets in "Findings record", one new bullet in
  "Tests", and one sentence in "Not in this task". The statements of
  fact in the new text agree with `runScriptStepWith` (resolution, then
  `statementClock`, then `Counters.firstUnknown`, then the run of the
  statement) and with the kind rule of plain INSERT (four cases that end
  the run, a success and a failure). No code changes; no tests.
- 2026-11-23: review `20261123T194711Z-3d577446` of the amendment gave
  3 "must" findings, all fixed in a `refactor:` commit. One result does
  not prove that the cases exclude each other. The text now says that
  the premises of different cases contradict, and that the pilot does
  not state this as a theorem. The step equation has the direction
  `runScriptStep … = result`. The data facts of `InsertFits` do not give
  the checks of the subqueries and of the cells. No code changes; no
  tests.
- 2026-11-23: the case type of plain INSERT is in the model.
  `StepCase.lean` holds the part for all statement kinds: the inductive
  `StepCase` with the cases `noClock`, `unknownCounter` and `checked`,
  which takes the cases of one kind as a parameter, and the theorems
  `StepCase.of_checks`, `StepCase.unique` and `RunStep.eq_of_cover`.
  `PlainInsertCase.lean` holds the cases of plain INSERT (`noTable`,
  `unready`, `success`, `failure`), one result
  (`PlainInsertCase.unique`), cover (`runScriptStep_plainInsert_cover`,
  proved from the kind rule) and the step equation
  (`runScriptStep_plainInsert_of_case`). The model root and the core
  globs of `lakefile.toml` include both modules. The "should" finding of
  review `20261123T194819Z-602f9059` (a long sentence in this file) is
  fixed here. Tests: `just dev-build`,
  `tests/test_model_package.py`, `tests/surface_layers_test.py`.
- 2026-11-23: review `20261123T195608Z-18dc743f` of the case type gave
  4 "must" findings on docstrings, all fixed in a `refactor:` commit:
  the success case names the database of the outcome, `unknownCounter`
  names the first unknown counter, `StepCase.of_checks` lists its three
  results, and `StepCase.unique` says that its premise is for every
  clock value. Tests: `just dev-build`.
- 2026-11-23: review `20261123T195806Z-29c82a5d` gave 3 "must" findings
  on the docstrings of `StepCase`, all fixed in a `refactor:` commit:
  the constructor `unknownCounter` names its clock premise, and
  `StepCase.of_checks` names only the counters that the statement reads
  and refers to `clockUnmodeled` with a checked reference. Tests:
  `just dev-build`.
- 2026-11-23: review `20261123T200007Z-e662b6d8` gave 1 "must" finding:
  "read order" does not name the order of
  `Resolved.Statement.counterReads`, which puts `changes()` first. The
  docstrings of `StepCase` now name that list; fixed in a `refactor:`
  commit. Tests: `just dev-build`.
- 2026-11-23: the second client test uses the case type.
  `tests/surface/Schema/Tests/ItemInsertCaseClaims.lean` proves the two
  INSERT claims of `ItemInsertClaims` with the same statements through
  `runScriptStep_plainInsert_of_case` and one case each, and names no
  kind rule and no case law. It also proves the claim for each input
  (`insert_done_or_error`: `.done 1` and the new row, or an error and
  the database before) with the cover `runScriptStep_plainInsert_cover`,
  and again (`insert_done_or_error_by_laws`) with a split on the key and
  the case-law claims of `ItemInsertClaims`. The root is in
  `tests/surface_fixture_roots.json` (`surfaceS6`), and
  `test_client_claims_on_items_use_the_case_type` in
  `tests/surface_schema_script_test.py` compiles it and expects four
  axiom reports. Tests: `tests/surface_schema_script_test.py`,
  `tests/surface_layers_test.py`,
  `tests/test_model_package.py::test_root_imports_the_core_and_only_the_prelude`.
- 2026-11-23: review `20261123T201356Z-24d517a0` gave 3 "should"
  findings, all fixed in a `refactor:` commit. The case-type fixtures
  join the chain of the first client test, so that each module compiles
  once; the test is now `test_client_claims_on_items_in_three_rule_forms`,
  and `test_client_claims_on_items_use_the_case_type` is gone. The test
  docstring gives the output and the database of each side of the claim
  for each input. The checks with the case type moved to the new
  fixture `ItemInsertCaseChecks.lean` (root in `surfaceS6`), so that
  their docstrings can list each premise and both files stay under 200
  lines. Tests: `tests/surface_schema_script_test.py`,
  `tests/surface_layers_test.py`.
