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
count is at the last pilot commit, before this record.

| Scope | Before | After | Change |
| --- | ---: | ---: | ---: |
| Model package | 59,152 | 59,162 | +10 |
| Surface package | 14,668 | 14,752 | +84 |
| Other packages and other Lean files | 3,693 | 3,693 | 0 |
| Tests | 19,992 | 20,501 | +509 |
| **Total** | **97,505** | **98,108** | **+603** |

The same change by origin:

| Part | Model | Surface | Tests |
| --- | ---: | ---: | ---: |
| Added once: projections, `step_rule`, `Connection` helpers, bridge, `sql_run` path | +59 | +185 | +56 |
| CREATE TABLE: rule, data facts, deleted laws, callers | −18 | −23 | +16 |
| Plain INSERT: rule, data lemmas, deleted laws, callers | −31 | −78 | −41 |
| Retention test of the deleted laws (task acceptance) | 0 | 0 | +235 |
| Client-claims test (task acceptance) | 0 | 0 | +243 |
| **Sum** | **+10** | **+84** | **+509** |

Notes:

- The model "once" lines are `StepRuleProjections.lean` (46),
  `StepRuleAttr.lean` (3) and `Connection.withDatabase` with
  `Connection.afterError_failed` (10).
- The surface "once" lines are `SqlRunKindRules.lean` (137),
  `KindRuleSend.lean` (45), `SqlRun.lean` and `SqlRunGoals.lean` (9),
  less the removed `sendRule` and `roleOf` entries (−6).
- The INSERT surface lines include the move of the generic part of
  `Reasoning/PlainInsertEffect.lean` (59) to `SendSingleStep.lean` (24).
- The two acceptance tests (478 lines) are new test content, not
  maintained proof work that a client needs.
- Without the two acceptance tests, the pilot changes the count by
  +125: +300 once, −25 for CREATE TABLE and −150 for INSERT.

Raw data: `after-scc.json`, `baseline-scc.json` and `scc-delta.tsv` in
the scratch directory of the session.

## Changed callers

Lines are added and removed lines of `jj diff --git` from the start
revision. The files of the new and deleted laws are not callers.

| Scope | Files | Added | Removed |
| --- | ---: | ---: | ---: |
| Model | 9 | 73 | 104 |
| Surface | 6 | 41 | 70 |
| Test fixtures | 10 | 219 | 235 |

- Model: `CreateSchemaSuccess`, `CreatedTables`, `PlainDeleteEffect`,
  `SchemaFailureLaws`, `StepContinuesOk`, `TableKeeps`, `DatabaseLaws`,
  `TableByName`, `PlainInsertSuccess`.
- Surface: `SqlRun`, `SqlRunGoals`, `SqlRunRules`, `PlainDeleteEffect`,
  `SchemaStepRules`, `SendStepRules`.
- Tests: `S6AutoSignup`, `SchemaRuleExamples`, `AddCustomerQueries`,
  `AddCustomerClaims`, `CustomerInsertSite`, `GlobalSignupInvariant`,
  `PlainInsertStepCases`, `S6AutoAddCustomer`, `SchemaCreateExamples`,
  `SignupInvariantClaims`. Each keeps its claims.
- `sql_run` proofs: three changed proofs (two in `S6AutoSignup`, one in
  `S6AutoAddCustomer`): the hints changed, the claims did not.
  `SchemaRuleExamples` keeps its claim with a new proof through the
  bridge and adds one `sql_run` proof of the same claim.

## Statement lines of the replaced laws

Lines from the theorem keyword to `:=`. The replacement column gives the
theorems that give the fact now; the retention test
(`tests/surface/Schema/Tests/ReplacedStepLaws.lean`,
`ReplacedSendLaws.lean`) proves each old statement from them.

| Replaced law | Before | Replacement | Lines |
| --- | ---: | --- | ---: |
| `runScriptStep_createTable` | 10 | `runScriptStep_createTable_eq` | 9 |
| `runScriptStep_createTable_ok` | 7 | `runScriptStep_createTable_eq`, `step_guards_hold` (kept) | 9 |
| `runScriptStep_createTable_frame` | 10 | `runScriptStep_createTable_eq`, `Database.tableNamed_createTable` | 13 |
| `runScriptStep_createTable_empty` | 6 | `runScriptStep_createTable_eq`, `Database.table_createTable_end` | 12 |
| `runScriptStep_insert_ok` | 16 | `runScriptStep_plainInsert_eq`, `insertReady_of_fits`, `insertOutcome_of_fits` | 37 |
| `plainInsert_database` | 14 | `runScriptStep_plainInsert_eq` | 30 |
| `runScriptStep_insert_ne_oneOf` | 8 | `runScriptStep_ne_oneOf_of_not_query` (kept) | 8 |
| `Sql.check_send_createTable` | 9 | `Sql.check_send_of_rule` with the CREATE TABLE rule | 16 |
| `Sql.check_send_plainInsert` | 22 | `Sql.check_send_of_rule` with the INSERT rule | 37 |
| `Sql.ifOk_send_plainInsert` | 18 | `Sql.check_send_of_rule` with the INSERT rule | 37 |

The ten replaced laws have 120 statement lines. The new theorems that
replace them have 60 statement lines in total: the two rules (9 and 30),
the bridge (7) and four data facts (14). Each new theorem serves several
replaced laws. The INSERT rule alone (30 lines) is longer than any law
that it replaces, because it states every case.

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

- **Concrete CREATE TABLE resolution.** `rfl` does not close the
  resolution equation of a concrete `CREATE TABLE` text;
  `with_unfolding_all rfl` does. So the hint `sql_run [rfl]` cannot
  close it. A concrete INSERT closes with `rfl` when the client gives
  the target and the cells.
- **Unnormalized cells.** When the resolution premise closes by `rfl`
  without the cells, the rule shows the cells as
  `Resolved.Cell.stored … ([…][0]?.getD …)`. The client then needs a
  normalization simp set or must give the cells.
- **The open goal `modeled`.** The client proves that the step
  continues by reducing the rule. `sql_run` now gives the rule as the
  hypothesis `rule`, so that the proof can rewrite the step without the
  name of the step function.
- **Client proofs.** The four client claims of
  `tests/surface/Schema/Tests/ItemInsertClaims.lean` use the kind rules,
  the bridge and data facts. They name `runScriptStep_plainInsert_eq`
  and `runScriptStep_createTable_eq`, whose names contain
  `runScriptStep`. The task bans the identifiers `runScriptStep`,
  `runScriptStepWith`, `resolveStatement` and `SqlState.statementRun`;
  no proof names one of them.
- **Data facts carry the work.** Most lines of the client test are data
  facts about the table (`ItemInsertSite.lean`,
  `ItemInsertOutcomes.lean`): readiness, fit, keys, counts. The rule
  needs them to select its case.

## Cost of the next kind

From the two kinds: the "once" part is done. A next kind needs:

- A rule file of 30 (a kind without data, as CREATE TABLE) to 85 code
  lines (a write kind, as plain INSERT), with a statement of 9 to 30
  lines.
- Data lemmas for the success case, about 10 to 30 lines, when the
  existing laws do not state them as functions on the database.
- No surface code: the bridge and `sql_run` do not depend on the kind.
  The kind's `Sql.check_send_…` rule and its `sendRule` and `roleOf`
  entries are deleted.
- Caller changes of about the size measured here: 5 to 10 files.

Estimate: a net change of −20 to −110 maintained lines for each kind.
Agent wall time in the pilot, from commit times: about 40 minutes for
CREATE TABLE with the projections, and about 15 minutes for the INSERT
rule, each with one or two review rounds after it. Kinds whose laws are shared
with other kinds (`runScriptStep_plainWrite_frame`, `_failed`) are
cheaper only when all kinds that share the law move together.
