# Statement rule pilot: findings

Audience: the team. Status: on 2026-11-23 the owner selected the kind
rule as the one maintained form; the pilot then removed the other two
forms. Contract:
[task](../../plans/20261123-statement-rule-pilot.task.md).
Start revision: `b7854558`. Last revision with the three forms:
`a03e8267`. Last code revision: `ee83eca7`.

The pilot replaces the step laws of CREATE TABLE and plain INSERT with
one exact kind rule for each kind, data facts and generic projections.
For plain INSERT, it then added two more forms for comparison: case laws
and a case type. This record gives the measurements, the facts that the
forms change, the comparison of the three forms of plain INSERT at
`a03e8267`, the owner decision, and the final measurement after the
removal of the two forms that the owner did not select.

## Owner decision of 2026-11-23

The owner compared the three forms in this record and selected the kind
rule as the one maintained form for plain INSERT and for the next
statement kinds. The commit `c519a705` removed the case laws
(`PlainInsertCases.lean`), the case type (`StepCase.lean`,
`PlainInsertCase.lean`) and the client test of the case type
(`ItemInsertCaseChecks.lean`, `ItemInsertCaseClaims.lean`). These stay:

- the data facts of a failed insertion (`PlainInsertFailure.lean`);
- the two INSERT claims of the client-claims test, proved with the kind
  rule and the data facts;
- the claim for each input, proved with the kind rule, in the new
  fixture `ItemInsertAnyClaims.lean`.

`runScriptStep_insert_ok` is a replaced law again, and the retention
test restates it. The commits after `c519a705` change only docstrings,
so the code lines of `c519a705` and `ee83eca7` are equal.

The sections "Case laws of plain INSERT", "Case type of plain INSERT"
and "Comparison of the three forms", and the measurements of the three
forms in the other sections, are a record of the state at `a03e8267`
on 2026-11-23.

## The forms

- Kind rules: `runScriptStep_createTable_eq`
  (`Programs/Scripts/CreateTableRule.lean`) and
  `runScriptStep_plainInsert_eq` (`Programs/Scripts/PlainInsertRule.lean`).
  Each has the resolution equation as its only premise and gives
  `runScriptStep … =` a term in which every case is visible. The simp set
  `step_rule` holds both.
- Data facts: `Database.table_createTable_end` and
  `Database.tableNamed_createTable`; for INSERT, `insertReady_of_fits`
  and `insertOutcome_of_fits`. Data facts of a failed insertion
  (`Schema/Writes/PlainInsertFailure.lean`):
  `LiteralData.insertCounts_error_changes`,
  `LiteralData.insertCounts_error_total`,
  `LiteralData.rowidsDistinct_eq_false_of_repeated` and
  `insertOutcome_constraintViolation`. They came with the case laws and
  stay after the owner decision.
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
- Removed after the owner decision: the case laws of plain INSERT
  (`Programs/Scripts/PlainInsertCases.lean`), the success law
  `runScriptStep_insert_ok` and the failure law
  `runScriptStep_insert_failed`.
- Removed after the owner decision: the case type of plain INSERT. The part for all statement kinds
  (`Programs/Scripts/StepCase.lean`): the inductive proposition
  `StepCase` with the cases `noClock`, `unknownCounter` and `checked`,
  and the theorems `StepCase.of_checks`, `StepCase.unique` and
  `RunStep.eq_of_cover`. The part for plain INSERT
  (`Programs/Scripts/PlainInsertCase.lean`): the inductive proposition
  `PlainInsertCase` with the cases `noTable`, `unready`, `success` and
  `failure`; one result `PlainInsertCase.unique`; cover
  `runScriptStep_plainInsert_cover`; and the step equation
  `runScriptStep_plainInsert_of_case`.

## Measurement method

The main measurement scripts are in the scratch directory of the session
(`/tmp/claude-1002/-home-codex-work/a1c729e8-ce7b-5ce0-94c1-8fab926cac49/scratchpad/pilot/`).
Each script reads a jj revision or the working copy. `SCRATCH` below is
that directory.

| Script | Command | Output |
| --- | --- | --- |
| `count_rev.py` | `python3 count_rev.py REV OUT.json` | scc 3.7.0 `Code` lines of each tracked `.lean` file of the revision, without the three frozen experiments (as `docs/development/lean-simplification-goal.md` counts), summed for each package and for `tests` |
| `scc_delta.py` | `python3 scc_delta.py OLD.json NEW.json` | the files whose code lines differ between two outputs of `count_rev.py` |
| `decl_code.py` | `python3 decl_code.py REV FILE NAME…` | for each declaration: its statement lines (from the keyword to the line that ends with `:=` or `:= by`) and its code lines (scc rules: no blank line, no comment, no docstring) |
| `time_modules.py` | `python3 time_modules.py PACKAGE:FILE…` | `lake lean FILE` in the package, two runs |
| `time_fixtures.py` | `python3 time_fixtures.py '[[MODULE…]]'` | the Lean compiler on each fixture of a chain, with its imports compiled before, two runs |

Times are the lower of two runs, in seconds. A model module time
includes the load of its imports, about 0.45 s; a surface module time
includes about 1.8 s.

Other sources, named where the record uses them:

- `decl_diff.py OLD NEW FILE:NAME[:NEWFILE[:N]]…`, run from the
  repository root as `python3 SCRATCH/decl_diff.py b7854558 94c3fa5e
  FILE:NAME…` with one argument for each declaration: the added and
  removed lines of each declaration with its docstring (section
  "Changed callers"). `NEWFILE` is the file at the new revision when the
  declaration moved, and `N` selects the `N`-th match from 0, for
  example `tests/surface/Programs/Reasoning/SchemaRuleExamples.lean:example::2`
  for the third `example` of that file, which gives +7/−3.
- `chain.py` and `probe_after_chain.py FILE M…`: compile the fixtures of
  a chain, then a scratch Lean file that imports them. The scratch file
  `kindany/KindAnyProbe.lean` held a proof of the claim for each input
  with the kind rule. Since `c519a705`, the fixture
  `ItemInsertAnyClaims.lean` holds this proof.
- The scratch files `funcases/Probe.lean` to `Probe4.lean`, compiled
  with `lake env lean FILE` in `packages/belay-sqlite-model` (sections
  "`fun_cases`" and "Comparison of the three forms").

`decl_code.py` miscounts the statement of a theorem whose proof is a
pattern match without `:=`, and of a theorem whose proof is on the line
of `:=`. Such statements are counted by hand: `StepCase.unique` (6
lines), `LiteralData.insertCounts_error_changes` and
`LiteralData.insertCounts_error_total` (3 lines each).

## Code lines

Totals of `count_rev.py` for the milestone revisions of the pilot. The
change from one milestone to the next is the net change of all commits
between them.

| Revision | Content | Model | Surface | Tests | Total |
| --- | --- | ---: | ---: | ---: | ---: |
| `b7854558` | start | 59,152 | 14,668 | 19,992 | 97,505 |
| `94c3fa5e` | kind rules, projections, bridge, retention test, client test | 59,162 | 14,752 | 20,501 | 98,108 |
| `67a9dc4b` | import fix of the surface path | 59,162 | 14,749 | 20,501 | 98,105 |
| `58a5b045` | case laws, client claims with the case laws | 59,242 | 14,749 | 20,474 | 98,158 |
| `cdb0da41` | case type | 59,388 | 14,749 | 20,474 | 98,304 |
| `18aa879d` | client test of the case type | 59,388 | 14,749 | 20,619 | 98,449 |
| `a03e8267` | last revision with the three forms | 59,388 | 14,749 | 20,619 | 98,449 |
| `ee83eca7` | case laws and case type removed; last code revision | 59,191 | 14,749 | 20,543 | 98,176 |

The other scopes do not change: SQL text package 1,945, conformance
package 1,042, public documentation tools package 134, other Lean files
(examples, tooling) 572.

The first measurement of the pilot was on `94c3fa5e`. The import fix
`67a9dc4b` then removed three counted import lines of the surface
package (`scc_delta.py` of the two revisions):

- `SqlRunKindRules.lean` −2: the import of `PlainInsertRule`, which only
  plain INSERT needs, and the import of `ResolvedStepGuards`, which the
  path of all kind rules needs.
- `KindRuleSend.lean` −1: the import of `StepRuleProjections`, which all
  kinds need.

For example, the case laws came in `7dbeba93` and the client test of the
case type in `24d517a0`; their lines are in the totals of `58a5b045` and
`18aa879d`. The removal came in `c519a705`; its lines are in the totals
of `ee83eca7`.

From `a03e8267` to `ee83eca7` (`scc_delta.py`, measured on 2026-11-23):
model −197 (`PlainInsertCase.lean` −96, `PlainInsertCases.lean` −52,
`StepCase.lean` −49), tests −76 (`ItemInsertCaseChecks.lean` −87,
`ItemInsertCaseClaims.lean` −58, `ItemInsertClaims.lean` −1, new
`ItemInsertAnyClaims.lean` +47, `ReplacedStepLaws.lean` +23). The
surface does not change.

### Change by origin

From `b7854558` to the last code revision `ee83eca7`, with
`scc_delta.py` of the two revisions (measured on 2026-11-23):

| Part | Model | Surface | Tests |
| --- | ---: | ---: | ---: |
| Added once: projections, `step_rule`, `Connection.afterError_failed`, bridge, `sql_run` path | +51 | +189 | +56 |
| Both pilot kinds: the shorter list `hintedKinds` | 0 | −1 | 0 |
| CREATE TABLE: rule, data facts, deleted laws, callers, the move of `Connection.withDatabase` | −16 | −26 | +16 |
| Plain INSERT kind rule: rule, data facts, deleted laws, callers | −25 | −81 | −41 |
| Data facts of a failed insertion (with their import in `Model.lean`) | +29 | 0 | 0 |
| Retention test of the deleted laws (task acceptance) | 0 | 0 | +235 |
| Client-claims test (task acceptance) | 0 | 0 | +285 |
| **Sum** | **+39** | **+81** | **+551** |

Notes on the final table:

- The rows "once", "both", CREATE TABLE and the INSERT kind rule are the
  same as in the table of `a03e8267` below; the notes below that table
  explain them.
- The data facts are `PlainInsertFailure.lean` (28). The model root
  `Model.lean` imports `PlainInsertRule` and `PlainInsertFailure` in
  place of the import of `PlainInsertStep` at the start revision (+1).
  At `a03e8267`, the root imported the two modules of the forms in its
  place, and the table there counts that line with the case type.
- The retention test is `ReplacedStepLaws.lean` (134) and
  `ReplacedSendLaws.lean` (101). It restates `runScriptStep_insert_ok`
  again (+23), as at `94c3fa5e`.
- The client-claims test is `ItemInsertSite.lean` (49),
  `ItemInsertOutcomes.lean` (57), `ItemInsertClaims.lean` (132) and
  `ItemInsertAnyClaims.lean` (47).

Without the acceptance tests (520 lines), the pilot adds 151 lines: 296
once (model 51, surface 189, tests 56), −1 for both kinds, −26 for
CREATE TABLE, −147 for the INSERT kind rule and +29 for the data facts
of a failed insertion. With the kind rules alone, as measured on
`94c3fa5e`, the change was +125: the import fix `67a9dc4b` later removed
3 lines, and the data facts add 29.

#### Change by origin at `a03e8267`, with the three forms

Measured on 2026-11-23, before the owner decision. From `b7854558` to
`a03e8267`, with `scc_delta.py` of the two revisions:

| Part | Model | Surface | Tests |
| --- | ---: | ---: | ---: |
| Added once: projections, `step_rule`, `Connection.afterError_failed`, bridge, `sql_run` path | +51 | +189 | +56 |
| Both pilot kinds: the shorter list `hintedKinds` | 0 | −1 | 0 |
| CREATE TABLE: rule, data facts, deleted laws, callers, the move of `Connection.withDatabase` | −16 | −26 | +16 |
| Plain INSERT kind rule: rule, data facts, deleted laws, callers | −25 | −81 | −41 |
| Plain INSERT case laws with their data facts | +80 | 0 | 0 |
| Case type, part for all statement kinds | +49 | 0 | 0 |
| Case type, part for plain INSERT (with its import in `Model.lean`) | +97 | 0 | 0 |
| Retention test of the deleted laws (task acceptance) | 0 | 0 | +212 |
| Client-claims test (task acceptance) | 0 | 0 | +239 |
| Client test of the case type (task acceptance) | 0 | 0 | +145 |
| **Sum** | **+236** | **+81** | **+627** |

Notes:

- The model "once" lines are `StepRuleProjections.lean` (46, less 6
  lines of `RunStep.continues` and `RunStep.continues_iff`, which moved
  unchanged from the model `PlainInsertEffect.lean` and count as zero),
  `StepRuleAttr.lean` (3) and `Connection.afterError_failed` (8).
- `Connection.withDatabase` (2 lines) moved from the surface package to
  the model package for the CREATE TABLE rule. Both sides of the move
  are in the CREATE TABLE line (model +2, surface −2), so they cancel.
- The surface "once" lines are `SqlRunKindRules.lean` (135, without
  imports of a kind), `KindRuleSend.lean` (44), `SqlRun.lean` (+7) and
  the function `closeFailure` of `SqlRunGoals.lean` (+3).
- `hintedKinds` in `SqlRunGoals.lean` lost the two pilot kinds; its
  list now fits in 3 lines instead of 4. The line belongs to both kinds
  together.
- `SqlRunRules.lean` loses 6 lines, all specific to a pilot kind: 3 for
  CREATE TABLE (its `sendRule` branch and its entry in `schemaKinds`)
  and 3 for INSERT (its `sendRule` branch and its import).
- The INSERT surface lines include the move of the generic part of
  `Reasoning/PlainInsertEffect.lean` (59) to `SendSingleStep.lean` (24).
  At `94c3fa5e` the INSERT surface lines were −80: they included the
  import of `PlainInsertRule` in `SqlRunKindRules.lean`, which `67a9dc4b`
  removed.
- The case laws are `PlainInsertCases.lean` (52) and
  `PlainInsertFailure.lean` (28). The case type is `StepCase.lean` (49)
  and `PlainInsertCase.lean` (96), with one import line in `Model.lean`.
- The retention test is `ReplacedStepLaws.lean` (111) and
  `ReplacedSendLaws.lean` (101). It was 235 lines at `94c3fa5e`; the
  case laws removed its restatement of `runScriptStep_insert_ok` (−23).
- The client-claims test is `ItemInsertSite.lean` (49),
  `ItemInsertOutcomes.lean` (57) and `ItemInsertClaims.lean` (133). It
  was 243 lines at `94c3fa5e`. The client test of the case type is
  `ItemInsertCaseChecks.lean` (87) and `ItemInsertCaseClaims.lean` (58).
- The three acceptance tests (596 lines) are new test content, not
  maintained proof work that a client needs.

At `a03e8267`, without the acceptance tests, the pilot added 348 lines: 296 once (model
51, surface 189, tests 56), −1 for both kinds, −26 for CREATE TABLE,
−147 for the INSERT kind rule, +80 for the case laws and +146 for the
case type. With the kind rules alone, as measured on `94c3fa5e`, the
change was +125: +298 once, −1 for both kinds, −26 for CREATE TABLE and
−146 for INSERT.

## Changed callers

A caller is an existing declaration that used a replaced law. The line
counts are the added and removed lines of each caller declaration with
its docstring (a line diff of the declaration text at the start
revision and at `94c3fa5e`; scratch script `decl_diff.py`). Imports,
module docstrings, moved declarations and the laws themselves are listed
apart. The case laws and the case type change no caller of the start
revision. The success law `runScriptStep_insert_ok` is a law of the
start revision with its statement and a new proof (section "Statement
lines of the replaced laws").

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
  - module docstrings that described the replaced form: the module
    docstring of `SchemaStepRules` listed CREATE TABLE among its rules,
    and the module docstring of `SendStepRules` named the replaced
    module `PlainInsertEffect`;
  - proof sketches that named a deleted law: three rules in
    `SchemaStepRules` named `Sql.check_send_createTable` (+9/−8 in the
    file, with its module docstring), and `Output.ofStep_delete_ne_oneOf`
    in the model `PlainDeleteEffect` named
    `Output.ofStep_insert_ne_oneOf`;
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
(9 and 30), the bridge with `Sql.sendReached_single` (7 and 4), the new
data facts `Database.table_createTable_end` (3), `insertReady_of_fits`
(3) and `insertOutcome_of_fits` (4), and the restated
`Database.tableNamed_createTable` (4). The INSERT rule alone (30 lines)
is longer than any law that it replaces, because it states every case.
The two INSERT send rules are restated through the kept generic send
laws, not through the bridge. The retention test uses none of the
generic projections; the callers and `sql_run` use them.

`runScriptStep_insert_ok` was a case law in the model between
`7dbeba93` and the owner decision, with the statement of the start
revision (16 statement lines). The retention test restates it at
`ee83eca7` with the same statement; its code lines went from 34 at the
start revision to 22 (`decl_code.py`): the proof uses the kind rule,
`insertReady_of_fits` and `insertOutcome_of_fits`.

## Case laws of plain INSERT

History: the owner decision removed the case laws in `c519a705`. The
data facts of the table stay. `decl_code.py a03e8267` on the two model
files, measured on 2026-11-23:

| Declaration | Statement | Code |
| --- | ---: | ---: |
| `runScriptStep_insert_ok` | 16 | 22 |
| `runScriptStep_insert_failed` | 19 | 25 |
| `LiteralData.insertCounts_error_changes` | 3 | 3 |
| `LiteralData.insertCounts_error_total` | 3 | 3 |
| `LiteralData.rowidsDistinct_eq_false_of_repeated` | 3 | 7 |
| `insertOutcome_constraintViolation` | 5 | 11 |
| **Sum** | **49** | **71** |

Each case law has a proof of 6 lines: it rewrites the step with the
kind rule and selects the case with its premises. The failure law has
the database before the statement in the error outcome; this loses no
case, because each error outcome of `insertOutcome` has the database
before (`insertOutcome_error`).

## Case type of plain INSERT

History: the owner decision removed the case type in `c519a705`.
`decl_code.py a03e8267` on the two model files, measured on 2026-11-23:

| Part | Declaration | Statement | Code |
| --- | --- | ---: | ---: |
| All kinds | `StepCase` | 10 | 10 |
| All kinds | `StepCase.of_checks` | 10 | 16 |
| All kinds | `StepCase.unique` | 6 | 16 |
| All kinds | `RunStep.eq_of_cover` | 2 | 3 |
| Plain INSERT | `PlainInsertCase` | 46 | 46 |
| Plain INSERT | `PlainInsertCase.unique` | 4 | 5 |
| Plain INSERT | `runScriptStep_plainInsert_cover` | 8 | 29 |
| Plain INSERT | `runScriptStep_plainInsert_of_case` | 8 | 11 |

The statement lines of an inductive proposition are its code lines: the
script counts 15 and 52 lines for the two types, with the docstrings of
the constructors. The part for all kinds has 45 code lines in its
declarations and 49 in its file; the part for plain INSERT has 91 and 96.

The success case names the outcome database `written`. By
`insertOutcome_ok`, `written` is the database of the kind rule,
`database.setRows target (LiteralData.inserted table values).rows`. The
cover proof uses this fact; a client that needs the rows applies it.

## Elaboration time

Package modules with `time_modules.py`. The first measurement was on
`94c3fa5e`. The case laws and the case type were measured on the model
of `cdb0da41`; the later commits do not change the model.

| Module | Before | After |
| --- | ---: | ---: |
| `CreateTableStepLaws` (deleted) | 0.65 | — |
| `PlainInsertStep` (deleted) | 0.68 | — |
| Model `PlainInsertEffect` (deleted) | 0.64 | — |
| `CreateTableRule` (new) | — | 0.59 |
| `PlainInsertRule` (new) | — | 0.84 |
| `StepRuleProjections` (new) | — | 0.48 |
| `StepRuleAttr` (new) | — | 0.45 |
| `PlainInsertCases` (case laws, removed in `c519a705`) | — | 0.63 |
| `PlainInsertFailure` (new, data facts of a failed insertion) | — | 0.43 |
| `StepCase` (case type for all kinds, removed in `c519a705`) | — | 0.51 |
| `PlainInsertCase` (case type for INSERT, removed in `c519a705`) | — | 0.75 |
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

Without the load of the imports, the case type takes about 0.06 s for
the part for all kinds and 0.3 s for the part for plain INSERT.

Fixtures that changed, with `time_fixtures.py`. The first measurement
was on `94c3fa5e`. The fixtures of the client tests and of the
retention test were measured again on `a03e8267`.

| Fixture | Before | After |
| --- | ---: | ---: |
| `S6AutoAddCustomer` | 1.78 | 1.41 |
| `S6AutoSignup` | 0.96 | 1.18 |
| `SchemaRuleExamples` | 2.18 | 5.02 |
| `CustomerInsertSite` | 1.04 | 1.13 |
| `PlainInsertStepCases` | 1.28 | 1.33 |
| `ReplacedStepLaws`, `ReplacedSendLaws` (new) | — | 0.41, 0.91 |
| `ItemInsertSite`, `ItemInsertOutcomes`, `ItemInsertClaims` (new) | — | 1.09, 1.32, 2.34 |
| `ItemInsertCaseChecks`, `ItemInsertCaseClaims` (removed in `c519a705`) | — | 1.06, 0.91 |
| `S6AutoKindRuleCases` (new) | — | 1.15 |

The other fixtures of the measured chains change by less than 0.1 s.

The fixtures of the two acceptance tests, measured again on the code of
`ee83eca7` (2026-11-23, `time_fixtures.py`): `ReplacedStepLaws` 0.41
(it restates `runScriptStep_insert_ok` again), `ReplacedSendLaws` 1.00,
`ItemInsertSite` 1.11, `ItemInsertOutcomes` 1.34, `ItemInsertClaims`
2.46 and the new `ItemInsertAnyClaims` 1.02.
`SchemaRuleExamples` has a new proof of an abstract CREATE TABLE claim
through the bridge and one new `sql_run` proof of the same claim, in
which `sql_run` closes the premise `modeled` with the guards of the
step. The rise of about 3 s comes with these two proofs; it was not
split further.

## Client claims at the last code revision

`decl_code.py ee83eca7`, measured on 2026-11-23. The client-claims test
proves its claims with the kind rules, the bridge and the data facts.
The two numbers that the comparison below gives for the kind rule, 74
and 40, are now measured numbers of repository files, not estimates
from earlier revisions and a scratch file.

| Declaration | File | Statement | Code |
| --- | --- | ---: | ---: |
| `insert_new_check` | `ItemInsertClaims.lean` | 11 | 22 |
| `new_key_inserts` | `ItemInsertClaims.lean` | 7 | 12 |
| `insert_taken_check` | `ItemInsertClaims.lean` | 11 | 20 |
| `taken_key_fails` | `ItemInsertClaims.lean` | 5 | 10 |
| `items_taken_outcome` | `ItemInsertOutcomes.lean` | 4 | 10 |
| **Two INSERT claims, subtotal** | | | **74** |
| `insert_any_rule` | `ItemInsertAnyClaims.lean` | 14 | 29 |
| `insert_done_or_error` | `ItemInsertAnyClaims.lean` | 5 | 11 |
| **Claim for each input** | | | **40** |

The two INSERT checks are those of `94c3fa5e`. They use
`items_taken_outcome` of the case laws (10 code lines), which has the
statement of `94c3fa5e` and gets the outcome from
`insertOutcome_constraintViolation`; the alias fact `items_aliases` is
not necessary. The check `insert_any_rule` and the claim
`insert_done_or_error` have the code of the scratch file
`kindany/KindAnyProbe.lean` and of `ItemInsertCaseClaims.lean` at
`a03e8267`. The claim for each input does not use `items_fits` or
`items_taken_outcome`. The site facts that the next section lists (63
code lines) do not change.

The other two claims of `ItemInsertClaims.lean` do not change:
`create_then_insert` (20) and `insert_keeps_names` (32).

## Client claims in the three forms

History, measured on 2026-11-23 before the owner decision. The two INSERT claims of the client-claims test ("a new key inserts",
"a taken key fails") with their helper theorems, in code lines of
`decl_code.py`. Each claim has the same statement in each form. The
table gives the declarations that differ between the forms; their sum
is a subtotal.

| Declaration | Kind rule (`94c3fa5e`) | Case laws (`a03e8267`) | Case type (`a03e8267`) |
| --- | ---: | ---: | ---: |
| check of a new key (`insert_new_check`, `insert_new_case`) | 22 | 22 | 20 |
| claim of a new key (`new_key_inserts`) | 12 | 12 | 12 |
| check of a taken key (`insert_taken_check`, `insert_taken_case`) | 20 | 21 | 17 |
| claim of a taken key (`taken_key_fails`) | 10 | 10 | 10 |
| outcome of a taken key (`items_taken_outcome`) | 13 | 10 | 10 |
| alias fact (`items_aliases`) | 2 | — | — |
| **Subtotal** | **79** | **75** | **69** |

All three forms also use these site facts, with the same code at both
revisions: `items_ready` (23) and `items_fits` (18) in
`ItemInsertOutcomes.lean`, and `items_table` (4), `items_values` (5),
`items_clock` (2), `items_reads` (1), `items_cellsReady` (1),
`items_counts_ok` (5) and `items_inserted` (4) in `ItemInsertSite.lean`:
63 code lines. These facts use the definitions and the other facts of
the two site modules (106 code lines together at `a03e8267`).

The data facts of the case laws (`insertOutcome_constraintViolation`,
`LiteralData.rowidsDistinct_eq_false_of_repeated`) shorten the outcome
of a taken key, and the alias fact is no longer necessary; the
case-type column uses the same outcome. The case laws state the values
of the rows with `let`, so their checks rewrite the values with
`items_values` in separate goals. In the case-type checks, the values
are an argument of the case, and `items_values` gives them in the
constructor. With the data facts of the case laws, the kind-rule
column is 74: the kind-rule checks use `items_taken_outcome` only by its
statement, which did not change, so its declaration of 10 code lines (4
statement lines and 6 proof lines) replaces the declaration of 13 code
lines and the alias fact (2).

The claim for each input (`insert_done_or_error`: the output is
`.done 1` with the inserted row, or an error output with the database
before) has two proofs in the client test and one in a scratch file:

| Proof | Declarations | Code lines |
| --- | --- | ---: |
| With the kind rule | the check `insert_any_rule` in the scratch file `kindany/KindAnyProbe.lean`, with the statement of `insert_any_case` (29); the claim with the proof of `insert_done_or_error` in `ItemInsertCaseClaims.lean`, with `insert_any_rule` in place of `insert_any_case` (11) | 40 |
| With the case laws | `insert_done_or_error_by_laws` (14), with the checks `insert_new_check` (22) and `insert_taken_check` (21) | 57 |
| With the case type | `insert_any_case` (42), `insert_done_or_error` (11) | 53 |

When the two checks of the case laws already exist, the proof with the
case laws adds 14 lines. It splits on whether a stored item has the id
as its rowid, and needs the fit facts of a new key and the outcome of a
taken key. The proofs with the kind rule and with the case type need
neither: they use the readiness of the table and the values
(`items_ready`) but not `items_fits` (18 lines) or
`items_taken_outcome` (10 lines). The proof with the kind rule
rewrites the step with the rule, reduces the clock, the counter, the
table and the readiness checks with the facts of the site, and splits
on the outcome. The proof with the case type splits the cover; the
cases `noClock`, `unknownCounter`, `noTable` and `unready` close by a
contradiction with the facts of the site. Neither proof was made as
short as possible.

The proof with the kind rule:

```lean
  unfold insertItem
  refine Sql.check_send_of_rule (runScriptStep_plainInsert_eq (target := 0) (rows := itemCells) (subqueries := [])
    (by rfl)) valid ?_ ?_
  all_goals
    dsimp only [Database.Raw.connection, List.headD]
    simp only [items_clock, items_reads, Counters.firstUnknown, items_table, items_values, items_ready rows valid.1,
      items_cellsReady, Resolved.subqueriesPlain, List.find?_nil, List.all_nil, Bool.and_self, ↓reduceIte]
  · split <;> rfl
  · split
    · rename_i written outcome
      rw [outcome, insertOutcome_ok outcome]
      refine Sql.sendReached_single (fun _ same => by cases same) fun _ => ?_
      simp only [items_counts_ok, items_inserted]
      exact done
    · exact Sql.sendReached_single (fun _ same => by cases same) fun _ => failed _ _
```

The proof with the case type:

```lean
  unfold insertItem
  generalize named : Syntax.Statement.insert _ _ _ _ = statement
  have cover := runScriptStep_plainInsert_cover (context := runContext) (clock := clock) (index := index)
    (connection := Database.Raw.connection { catalog := itemsCatalog, rows } counters) (statement := statement)
    (target := 0) (rows := itemCells) (subqueries := []) (parameters := [.integer id.toInt, .text name.toUTF8.toList])
    (by rw [← named]; rfl)
  obtain ⟨result, step, cover⟩ : ∃ result, _ = result ∧ StepCase _ _ _ _ _ result := ⟨_, rfl, cover⟩
  cases cover with
  | noClock timed => simp [items_clock] at timed
  | unknownCounter timed unknown => simp [items_reads, Counters.firstUnknown] at unknown
  | checked timed known case =>
    dsimp only [Database.Raw.connection] at case
    cases case with
    | noTable located => simp [items_table] at located
    | unready located evaluated unready =>
      obtain rfl := Option.some.inj ((items_table rows).symm.trans located)
      obtain rfl := (items_values _ _ _ id name).symm.trans evaluated
      simp [items_ready rows valid.1, items_cellsReady, Resolved.subqueriesPlain] at unready
    | success located evaluated ready plain cells outcome =>
      obtain rfl := Option.some.inj ((items_table rows).symm.trans located)
      obtain rfl := (items_values _ _ _ id name).symm.trans evaluated
      obtain rfl := insertOutcome_ok outcome
      refine Sql.check_send_of_rule step valid rfl (Sql.sendReached_single (fun _ same => by cases same) fun _ => ?_)
      simp only [items_counts_ok, items_inserted]
      exact done
    | failure located evaluated ready plain cells outcome =>
      exact Sql.check_send_of_rule step valid rfl (Sql.sendReached_single (fun _ same => by cases same)
        fun _ => failed _ _)
```

Two points of this proof are not obvious:

- Lean does not infer the statement of `runScriptStep_plainInsert_cover`
  from its resolution premise, so the proof must give the statement.
  The fixture gives it with `generalize`, so that it does not repeat the
  concrete syntax of the INSERT; the resolution premise then closes with
  `rw [← named]; rfl`.
- `cases` cannot split the cover while its result is the step term
  ("dependent elimination failed"). The `obtain` line gives the result
  a name and keeps the step equation `step` for the bridge. The proof
  names no step function.

## `fun_cases`

Lean 4.34.1 generates `runScriptStepWith.fun_cases`. The pilot tried it
in scratch files (`funcases/Probe.lean`, `Probe2.lean`) and did not use
it in the code.

- `unfold runScriptStep; fun_cases runScriptStepWith` splits a goal
  about a step into five cases: a resolution error, no clock, an unknown
  counter, `(!run.ready) = true`, and the run that is ready. In each
  case, the goal shows the result of that case.
- The hypotheses of the cases have no names (`x✝`), and the cases have
  no names from the model.
- The cases include the resolution error and do not fix the resolved
  statement to an INSERT.
- The last case is not split further. `runStatement.fun_cases` splits on
  the statement kind and the table, and `insertOutcome.fun_cases` on the
  alias mismatch and the constraint check. Each is a separate function,
  so the INSERT checks `insertReady`, `subqueriesPlain` and `cellsReady`
  are not cases of their own.
- `runScriptStep.fun_cases` gives no split: `runScriptStep` applies
  `runScriptStepWith` and has no match.
- `fun_cases` is a tactic step, not a theorem: it gives no cover object
  that a proof can pass to another theorem, and no equation for one
  case. It costs no maintained lines.

A cover proof with `fun_cases` instead of the kind rule was not tried.

## Comparison of the three forms

History: the comparison at `a03e8267`, measured on 2026-11-23, which the
owner used for the decision.

| | Kind rule | Case laws | Case type |
| --- | --- | --- | --- |
| Model code lines for plain INSERT | 84 (the rule file; rule 30 statement and 78 code lines) | +80 on the kind rule (28 of them data facts) | +146 on the kind rule (49 once for all kinds, 97 for INSERT) |
| Elaboration of its modules | 0.84 s | 0.63 s and 0.43 s | 0.51 s and 0.75 s |
| Two INSERT claims, subtotal of the declarations that differ | 79 (74 with the data facts of the case laws) | 75 | 69 |
| Claim for each input | 40 (scratch) | 57 (14 when the two checks exist) | 53 |
| Inputs covered | all, as one term | one case each: success, failure | all, as named cases |

What each form gives that the other two do not:

- The kind rule gives the step as one term for each input. `simp` and
  `rw` can compute with it, `sql_run` applies it through the set
  `step_rule`, and the generic projections take it. It is the only form
  whose proof unfolds the step function; the other two forms are proved
  from it. In the pilot, it gives the shortest proof of the claim for
  each input.
- The case laws give no fact that the case type does not give. The
  success law takes `InsertFits`, which gives the readiness check of
  the table and the values (`LiteralData.insertReady`) and the
  successful outcome; the caller supplies the plain subqueries and the
  ready cells. With the case type, the client gets the readiness check
  and the outcome from `insertReady_of_fits` and
  `insertOutcome_of_fits`. The failure law takes the readiness checks
  and an error outcome, as the case `failure` does.
- The case type gives cover: each input is in a named case, with named
  premises, and a proof for each input splits on the cases with `cases`
  or `rcases`. It also gives one result, and it states the checks of
  the clock and the counters once for all kinds. The equation of each
  case comes from one theorem, `runScriptStep_plainInsert_of_case`.

Which form derives from which:

- Case laws from the kind rule: a proof of 6 lines for each law, as in
  `PlainInsertCases.lean`.
- Case laws from the case type: one term for each law. The scratch file
  `funcases/Probe3.lean` proves both with the statements of the model,
  for example the failure law with
  `fun ready checked failed => runScriptStep_plainInsert_of_case found
  (.checked timed known (.failure located rfl checked plain ready failed))`.
  Each law keeps its statement of 16 or 19 lines.
- Case type from the kind rule: the cover proof (29 code lines), with
  `StepCase.of_checks`. One result (5) and the step equation (11) do not
  use the kind rule.
- Kind rule from the case type: a proof of 21 lines. The scratch file
  `funcases/Probe4.lean` proves the statement of
  `runScriptStep_plainInsert_eq`: its first line applies
  `runScriptStep_plainInsert_of_case`, and the other 20 lines, which
  give the case of each branch of the right side, are the lines of the
  cover proof after its first line. In the model, the cover is
  proved from the kind rule, so this derivation needs another proof of
  the cover to stand alone.
- Case type and kind rule from the case laws: not possible. The case
  laws state no case in which the run ends.

For the decision, the record listed what a next kind needs under the
case type. The owner did not select the case type. A next kind under
the case type needs:

- its kind rule, for the cover proof and for `sql_run`: 30 code lines
  for a kind without data, as CREATE TABLE, to 84 for a write kind, as
  plain INSERT;
- its case inductive proposition, with the cases of the kind after the
  two checks (46 code lines for plain INSERT);
- its one result (5 for plain INSERT);
- its cover, proved from its kind rule with `StepCase.of_checks` (29 for
  plain INSERT);
- its step equation, with `RunStep.eq_of_cover` and
  `StepCase.unique` (11).

The part for all kinds (`StepCase.lean`) is done. A next kind needs no
case laws.

In plain numbers: on top of the kind rule, the case type costs 97 model
lines for plain INSERT and 49 once, and saves 5 lines on the two
INSERT claims against the kind rule with the same data facts, and 6
against the case laws. For
the claim for each input, the proof with the kind rule is 13 lines
shorter than the proof with the case type.

The owner selected the kind rule on 2026-11-23 as the one maintained
form of each kind, with data facts for the outcomes of the kind such as
those of `PlainInsertFailure.lean`, and with neither case laws nor a
case type. The comparison gave these reasons: in this pilot, the case
type saves 5 lines of client proof on the two INSERT claims together and
costs about 90 model lines for each write kind, and the kind rule gives
the shortest proof of the claim for each input.

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
- **Client proofs.** The task bans the identifiers `runScriptStep`,
  `runScriptStepWith`, `resolveStatement` and `SqlState.statementRun`;
  no proof of the client tests names one of them. Some proofs name
  theorems whose names start with `runScriptStep`:
  - in `ItemInsertClaims.lean`, the INSERT checks name the kind rule
    `runScriptStep_plainInsert_eq`, and the program that creates a
    table names `runScriptStep_createTable_eq`;
  - in `ItemInsertAnyClaims.lean`, the check `insert_any_rule` names
    `runScriptStep_plainInsert_eq`.

  At `a03e8267`, the INSERT checks of `ItemInsertClaims.lean` named the
  case laws, and the checks of `ItemInsertCaseChecks.lean` named
  `runScriptStep_plainInsert_of_case` and
  `runScriptStep_plainInsert_cover`.
- **Data facts carry the work.** Of the 285 code lines of the
  client-claims test at `ee83eca7`, 106 are in the two modules of the
  site and its data facts (`ItemInsertSite.lean` 49,
  `ItemInsertOutcomes.lean` 57: the definitions of the table and the
  statement, and readiness, fit, keys, counts). The readiness and
  outcome facts select the case; the row and count facts give its
  result for the claim. The modules of the claims have 132 lines
  (`ItemInsertClaims.lean`, with its helper checks and program
  definitions) and 47 lines (`ItemInsertAnyClaims.lean`).

## Answers to the pilot questions

- **Does the form lose a fact that a caller can prove today?** No. The
  retention test proves the ten replaced laws with their premises of
  the start revision, from the kind rules and the data facts.
- **How many code lines does it remove and add, once and for each
  kind?** At the last code revision `ee83eca7`: once +296 (model 51,
  surface 189, tests 56); CREATE TABLE −26; plain INSERT with the kind
  rule −147, and +29 for the data facts of a failed insertion; both
  kinds −1. The acceptance tests add 520. At `a03e8267`, the two forms
  that the owner did not select added 80 (case laws) and 146 (case
  type, 49 of them once for all kinds).
- **Can a client prove claims about programs without the step function
  in the proof?** Yes: no client proof names a banned identifier. With
  the kind rule, the declarations that differ for the two INSERT claims
  take 74 code lines, and the claim for each input takes 40
  (`insert_any_rule` 29 and `insert_done_or_error` 11 in
  `ItemInsertAnyClaims.lean`), measured in the repository files of
  `ee83eca7`. At `a03e8267`, the two INSERT claims took 75 lines with
  the case laws and 69 with the case type, and the claim for each input
  took 57 with the case laws and 53 with the case type.

## Cost of the next kind

From the two kinds: the "once" part is done. A next kind in the selected
form needs:

- A rule file of 30 (a kind without data, as CREATE TABLE) to 84 code
  lines (a write kind, as plain INSERT), with a statement of 9 to 30
  lines.
- Data lemmas for the success case, about 10 to 30 lines, when the
  existing laws do not state them as functions on the database.
- Data facts for the failure outcomes of a kind that can fail, as the
  28 lines of `PlainInsertFailure.lean` for plain INSERT.
- No case laws and no case type.
- No surface code: the bridge and `sql_run` do not depend on the kind.
  The kind's `Sql.check_send_…` rule and its `sendRule` and `roleOf`
  entries are deleted.
- Caller changes. For the two pilot kinds together: 4 model and 12
  test declarations, and one tactic function.

In the pilot, without the acceptance tests, the net change was −26
lines for CREATE TABLE and −147 for plain INSERT with the kind rule,
and +29 for the data facts of a failed insertion. Estimate for a next
kind: a net change in that range, larger when the kind has more
replaced laws and callers.
Agent wall time in the pilot, from commit times: about 40 minutes for
CREATE TABLE with the projections, followed by three review rounds, and
about 15 minutes for the INSERT rule, followed by two review rounds.
Kinds whose laws are shared with other kinds
(`runScriptStep_plainWrite_frame`, `_failed`) are cheaper only when all
kinds that share the law move together.
