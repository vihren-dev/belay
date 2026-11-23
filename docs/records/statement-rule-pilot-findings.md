# Statement rule pilot: findings

Audience: the team. Status: measured on the pilot commits; the owner
decides on the form. Contract:
[task](../../plans/20261123-statement-rule-pilot.task.md).
Start revision: `b7854558`.

The pilot replaces the step laws of CREATE TABLE and plain INSERT with
one exact kind rule for each kind, data facts and generic projections.
This record gives the measurements and the facts that the new form
changes.

## The form

- Kind rules: `runScriptStep_createTable_eq`
  (`Programs/Scripts/CreateTableRule.lean`) and
  `runScriptStep_plainInsert_eq` (`Programs/Scripts/PlainInsertRule.lean`).
  Each has the resolution equation as its only premise and gives
  `runScriptStep … =` a term in which every case is visible. The simp set
  `step_rule` holds both.
- Data facts: `Database.table_createTable_end` and
  `Database.tableNamed_createTable`; for INSERT, `insertReady_of_fits`
  and `insertOutcome_of_fits`.
- Generic projections (`Programs/Scripts/StepRuleProjections.lean`):
  `RunStep.of_rule`, `continued_of_rule`, `continues_of_rule`,
  `others_of_rule`, `ne_oneOf_of_rule`, `isError_of_rule`,
  `continuing_ite`.
- Surface bridge: `Sql.check_send_of_rule`
  (`packages/belay/Belay/Sqlite/Programs/Scripts/KindRuleSend.lean`).
  `sql_run` finds the rules of the set `step_rule` and applies them
  through the bridge (`Automation/SqlRunKindRules.lean`).
  `SqlRunRules.lean` has no `sendRule` entry and no `roleOf` names for
  the two kinds.

## Code lines

Counter: scc 3.7.0, sum of `Code` of the tracked `.lean` files, without
the three frozen experiments (as
`docs/development/lean-simplification-goal.md` counts). The "after"
count is on the code of commit `94c3fa5e` (`rkwwvmpt`); the later
commits of the pilot change only comments and documents.

| Scope | Before | After | Change |
| --- | ---: | ---: | ---: |
| Model package | 59,152 | 59,162 | +10 |
| Surface package | 14,668 | 14,752 | +84 |
| SQL text package | 1,945 | 1,945 | 0 |
| Conformance package | 1,042 | 1,042 | 0 |
| Public documentation tools package | 134 | 134 | 0 |
| Other Lean files (examples, tooling) | 572 | 572 | 0 |
| Tests | 19,992 | 20,501 | +509 |
| **Total** | **97,505** | **98,108** | **+603** |

The same change by origin:

| Part | Model | Surface | Tests |
| --- | ---: | ---: | ---: |
| Added once: projections, `step_rule`, `Connection.afterError_failed`, bridge, `sql_run` path | +51 | +191 | +56 |
| CREATE TABLE: rule, data facts, deleted laws, callers, the move of `Connection.withDatabase` | −16 | −26 | +16 |
| Plain INSERT: rule, data lemmas, deleted laws, callers | −25 | −81 | −41 |
| Retention test of the deleted laws (task acceptance) | 0 | 0 | +235 |
| Client-claims test (task acceptance) | 0 | 0 | +243 |
| **Sum** | **+10** | **+84** | **+509** |

Notes:

- The model "once" lines are `StepRuleProjections.lean` (46, less 6
  lines of `RunStep.continues` and `RunStep.continues_iff`, which moved
  unchanged from the model `PlainInsertEffect.lean` and count as zero),
  `StepRuleAttr.lean` (3) and `Connection.afterError_failed` (8).
- `Connection.withDatabase` (2 lines) moved from the surface package to
  the model package for the CREATE TABLE rule. Both sides of the move
  are in the CREATE TABLE line (model +2, surface −2), so they cancel.
- The surface "once" lines are `SqlRunKindRules.lean` (137),
  `KindRuleSend.lean` (45), and `SqlRun.lean` with `SqlRunGoals.lean`
  (9).
- `SqlRunRules.lean` loses 6 lines, all specific to a pilot kind: 3 for
  CREATE TABLE (its `sendRule` branch and its entry in `schemaKinds`)
  and 3 for INSERT (its `sendRule` branch and its import).
- The INSERT surface lines include the move of the generic part of
  `Reasoning/PlainInsertEffect.lean` (59) to `SendSingleStep.lean` (24).
- The two acceptance tests (478 lines) are new test content, not
  maintained proof work that a client needs.
- Without the two acceptance tests, the pilot changes the count by
  +125: +298 once, −26 for CREATE TABLE and −147 for INSERT.

Raw data: `after-scc.json`, `baseline-scc.json` and `scc-delta.tsv` in
the scratch directory of the session.

## Changed callers

A caller is an existing declaration that used a replaced law. The line
counts are the added and removed lines of each caller declaration with
its docstring (a line diff of the declaration text at the start
revision and now; scratch script `decl_diff.py`). Imports, module
docstrings, moved declarations and the laws themselves are listed apart.

| Scope | Changed callers | Added | Removed |
| --- | ---: | ---: | ---: |
| Model | 4 | 26 | 11 |
| Surface rules | 0 | 0 | 0 |
| `sql_run` (`sendRule`) | 1 | 1 | 5 |
| Test fixtures | 12 | 132 | 157 |

- Model callers: `runScriptStep_create_ok` (`CreateSchemaSuccess`),
  `runScriptStep_createTable_failed` (`SchemaFailureLaws`),
  `runScriptStep_keepsTable` (`TableKeeps`) and
  `runScriptStep_createdTables` (`CreatedTables`).
- Test callers, each with the same claim:
  `signup_keeps_by_sql_run`, `signup_keeps_global_by_sql_run`
  (`S6AutoSignup`), the abstract CREATE TABLE example of
  `SchemaRuleExamples`, `addCustomer_adds` (`AddCustomerClaims`),
  `insert_then_holds` (`CustomerInsertSite`), `signup_keeps_global`
  (`GlobalSignupInvariant`), `two_rows` (`PlainInsertStepCases`),
  `addCustomer_adds_by_sql_run`, `addCustomer_adds_by_rules`,
  `addCustomer_adds_triple` (`S6AutoAddCustomer`),
  `create_appends_and_keeps` (`SchemaCreateExamples`), `signup_keeps`
  (`SignupInvariantClaims`).
- `sendRule` (`SqlRunRules`) named the two deleted surface rules. The
  other changes of the tactic support the new path and are not callers:
  `schemaKinds` (+3/−4) and the import in `SqlRunRules`, `hintedKinds`
  and `closeFailure` in `SqlRunGoals` (+12/−8 in the file), and
  `runSend` in `SqlRun` (+13/−3 in the file).
- Not in the counts:
  - imports of `PlainDeleteEffect` (model and surface),
    `CreatedTables`, `StepContinuesOk` and `SendStepRules`;
  - docstrings that named a deleted law: the module and three other
    rules in `SchemaStepRules` (+9/−8), and `PlainDeleteEffect` and
    `SendStepRules`;
  - three declarations that moved unchanged to the file of their other
    users: `customer_named_after_insert`,
    `AccountSignupSite.keeps_of_valid` and
    `GlobalSignupSite.keeps_of_valid`;
  - the new `sql_run` example of `SchemaRuleExamples` (+6, with a
    comment of 2 lines);
  - the laws: the deleted `runScriptStep_createTable_empty`,
    `runScriptStep_createTable_ok` and `Sql.check_send_createTable`;
    `runStatement_insert_ok`, replaced by `insertOutcome_of_fits` and
    `insertReady_of_fits`; `Database.table_createTable` and
    `Database.tableNamed_createTable`, restated with
    `Database.createTable`; the move of `Connection.withDatabase`.
- `sql_run` proofs: four existing proofs changed, two in `S6AutoSignup`
  and two in `S6AutoAddCustomer` (`addCustomer_adds_by_sql_run` and
  `addCustomer_adds_triple`: their hints and their `modeled` and
  `success` cases). The claims did not change.

## Statement lines of the replaced laws

Lines from the theorem keyword to the `:=` that starts the proof. The
retention test (`tests/surface/Schema/Tests/ReplacedStepLaws.lean`,
`ReplacedSendLaws.lean`) proves each old statement. "New" lists the
theorems that the pilot adds or restates and that the proof uses, with
the sum of their statement lines. "Kept" lists the theorems of the
start revision that the proof uses unchanged, with their statement
lines.

| Replaced law | Before | New (lines) | Kept (lines) |
| --- | ---: | --- | --- |
| `runScriptStep_createTable` | 12 | `runScriptStep_createTable_eq` (9) | none |
| `runScriptStep_createTable_ok` | 7 | `runScriptStep_createTable_eq` (9) | `step_guards_hold` (5) |
| `runScriptStep_createTable_frame` | 10 | `runScriptStep_createTable_eq`, the restated `Database.tableNamed_createTable` (13) | none |
| `runScriptStep_createTable_empty` | 6 | `runScriptStep_createTable_eq`, `Database.table_createTable_end` (12) | none |
| `runScriptStep_insert_ok` | 16 | `runScriptStep_plainInsert_eq`, `insertReady_of_fits`, `insertOutcome_of_fits` (37) | none |
| `plainInsert_database` | 14 | `runScriptStep_plainInsert_eq` (30) | none |
| `runScriptStep_insert_ne_oneOf` | 8 | none (0) | `runScriptStep_ne_oneOf_of_not_query` (8) |
| `Sql.check_send_createTable` | 12 | `runScriptStep_createTable_eq`, `Sql.check_send_of_rule`, `Sql.sendReached_single` (20) | `step_guards_hold` (5) |
| `Sql.check_send_plainInsert` | 22 | `runScriptStep_plainInsert_eq`, through the restated `plainInsert_database` (30) | `Sql.check_send_of_step` (14), `runScriptStep_effect` (14), `runScriptStep_plainWrite_failed` (10), `runScriptStep_ne_oneOf_of_not_query` (8), `runScriptStep_continued` (4): 50 |
| `Sql.ifOk_send_plainInsert` | 18 | `runScriptStep_plainInsert_eq`, through the restated `plainInsert_database` (30) | `check_send_single_of_step` (9), `runScriptStep_ne_oneOf_of_not_query` (8), `runScriptStep_valid` (6), `ExecutionContext.initial_holds_valid` (2): 25 |

The ten replaced laws have 125 statement lines. The distinct new and
restated theorems of the table have 64 statement lines: the two rules
(9 and 30), the bridge with `Sql.sendReached_single` (7 and 4), three new
data facts (10) and the restated `Database.tableNamed_createTable` (4).
The INSERT rule alone (30 lines) is longer than any law that it
replaces, because it states every case. The two INSERT send rules are
restated through the kept generic send laws, not through the bridge.
The retention test uses none of the generic projections; the callers
and `sql_run` use them.

## Elaboration time

Seconds, the lower of two runs. Package modules: `lake lean FILE`; the
time includes the load of the imports (about 0.45 s for a model module
and 1.8 s for a surface module). Fixtures: the Lean compiler on the
module with its imports prebuilt. Raw data: `baseline-timing-*.tsv` and
`after-timing-*.tsv` in the scratch directory.

| Module | Before | After |
| --- | ---: | ---: |
| `CreateTableStepLaws` (deleted) | 0.65 | — |
| `PlainInsertStep` (deleted) | 0.68 | — |
| Model `PlainInsertEffect` (deleted) | 0.64 | — |
| `CreateTableRule` (new) | — | 0.59 |
| `PlainInsertRule` (new) | — | 0.84 |
| `StepRuleProjections` (new) | — | 0.48 |
| `StepRuleAttr` (new) | — | 0.45 |
| `StepContinuesOk` | 0.62 | 0.63 |
| `CreatedTables` | 0.78 | 0.79 |
| `PlainInsertSuccess` | 0.51 | 0.46 |
| `TableKeeps` | 0.86 | 0.87 |
| `SchemaFailureLaws` | 0.62 | 0.61 |
| `CreateSchemaSuccess` | 0.84 | 0.85 |
| `PlainInsertStepRule` (deleted) | 1.80 | — |
| `Reasoning/PlainInsertEffect` (now `SendSingleStep`) | 1.82 | 1.81 |
| `KindRuleSend` (new) | — | 1.78 |
| `SqlRunKindRules` (new) | — | 2.53 |
| `SchemaStepRules` | 1.82 | 1.79 |
| `SqlRunRules` | 2.09 | 2.06 |
| `SqlRunGoals` | 2.54 | 2.57 |
| `SqlRun` | 2.33 | 2.40 |

Fixtures that changed:

| Fixture | Before | After |
| --- | ---: | ---: |
| `S6AutoAddCustomer` | 1.78 | 1.41 |
| `S6AutoSignup` | 0.96 | 1.18 |
| `SchemaRuleExamples` | 2.18 | 5.02 |
| `CustomerInsertSite` | 1.04 | 1.13 |
| `PlainInsertStepCases` | 1.28 | 1.33 |
| `ReplacedStepLaws`, `ReplacedSendLaws` (new) | — | 0.41, 0.91 |
| `ItemInsertSite`, `ItemInsertOutcomes`, `ItemInsertClaims` (new) | — | 1.09, 1.33, 2.45 |
| `S6AutoKindRuleCases` (new) | — | 1.15 |

The other fixtures of the measured chains change by less than 0.1 s.
`SchemaRuleExamples` has a new proof of an abstract CREATE TABLE claim
through the bridge and one new `sql_run` proof of the same claim, in
which `sql_run` closes the premise `modeled` with the guards of the
step. The rise of about 3 s comes with these two proofs; it was not
split further.

## Lost or weakened facts

None. The retention test proves the statement of each of the ten
replaced laws, copied from the start revision, with the same premises.
The partial laws keep their weak premises: `runScriptStep_createTable`
and `plainInsert_database` follow from the rule and a step that
continues, without validity.

## Findings

- **Concrete CREATE TABLE resolution.** In a hand proof, `rfl` does not
  close the resolution equation of a concrete `CREATE TABLE` text;
  `with_unfolding_all rfl` does. `sql_run [rfl]` closes it, because
  `sql_run` tries each hint also under `with_unfolding_all`
  (`SqlRunGoals.lean`; `SchemaRuleExamples.allKinds_closes_the_transaction`
  uses it). A concrete INSERT closes with `rfl` when the client gives
  the target and the cells.
- **Unnormalized cells.** When the resolution premise closes by `rfl`
  without the cells, the rule shows the cells as
  `Resolved.Cell.stored … ([…][0]?.getD …)`. The client then needs a
  normalization simp set or must give the cells.
- **The open goal `modeled`.** The client proves that the step
  continues by reducing the rule. `sql_run` now gives the rule as the
  hypothesis `rule`, so that the proof can rewrite the step without the
  name of the step function.
- **Client proofs.** The proofs of the four client claims of
  `tests/surface/Schema/Tests/ItemInsertClaims.lean` use the kind rules,
  the bridge, `sql_run` and data facts. Three of them name
  `runScriptStep_plainInsert_eq` or `runScriptStep_createTable_eq`
  (through their helper checks), whose names contain
  `runScriptStep`. The task bans the identifiers `runScriptStep`,
  `runScriptStepWith`, `resolveStatement` and `SqlState.statementRun`;
  no proof names one of them.
- **Data facts carry the work.** Of the 243 code lines of the client
  test, 111 are in the two modules of the site and its data facts
  (`ItemInsertSite.lean` 51, `ItemInsertOutcomes.lean` 60: the
  definitions of the table and the statement, and readiness, fit, keys,
  counts). The readiness and outcome facts select the case of the rule;
  the row and count facts give its result for the claim. The module of
  the claims (`ItemInsertClaims.lean`) has 132 lines, with its helper
  checks and program definitions.

## Cost of the next kind

From the two kinds: the "once" part is done. A next kind needs:

- A rule file of 30 (a kind without data, as CREATE TABLE) to 84 code
  lines (a write kind, as plain INSERT), with a statement of 9 to 30
  lines.
- Data lemmas for the success case, about 10 to 30 lines, when the
  existing laws do not state them as functions on the database.
- No surface code: the bridge and `sql_run` do not depend on the kind.
  The kind's `Sql.check_send_…` rule and its `sendRule` and `roleOf`
  entries are deleted.
- Caller changes. For the two pilot kinds together: 4 model and 12
  test declarations, and one tactic function.

In the pilot, without the acceptance tests, the net change was −26
lines for CREATE TABLE and −147 for plain INSERT. Estimate for a next
kind: a net change in that range, larger when the kind has more
replaced laws and callers.
Agent wall time in the pilot, from commit times: about 40 minutes for
CREATE TABLE with the projections, followed by three review rounds, and
about 15 minutes for the INSERT rule, followed by two review rounds.
Kinds whose laws are shared with other kinds
(`runScriptStep_plainWrite_frame`, `_failed`) are cheaper only when all
kinds that share the law move together.
