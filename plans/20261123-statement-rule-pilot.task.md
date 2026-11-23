# Pilot: one exact rule for each statement kind

Created 2026-11-23. Started.
Status: [20261123-statement-rule-pilot.status.md](20261123-statement-rule-pilot.status.md).
[Belay issue 468](https://github.com/vihren-dev/belay/issues/468).

The model has 99 theorems about `runScriptStep`. Most of them state one
fact about one statement kind, and each repeats the resolution premise,
the step premise and their binders. A client proof about a program needs
a further surface rule for each kind (`Sql.check_send_…`), and `sql_run`
holds a table of these rules and of the names of their premises.

This pilot builds a different form for two kinds, CREATE TABLE and plain
INSERT, and measures it. A plain INSERT is a resolved
`.insert target rows [] subqueries none`: no RETURNING clause and no
write rules. The form has three parts:

- A kind rule. For a statement that resolves to the kind, one theorem
  gives the result of `runScriptStep` in every case: when the run ends,
  and for a step that continues its output, its next connection and its
  further executions.
- Data facts. A fact about the database after the statement is a theorem
  about a function on databases or tables. It does not mention a step.
- Generic projections. A fact that today is one law for each kind, such
  as "the step has no further execution" or "the output is not a
  choice", follows from the kind rule by a theorem that does not depend
  on the kind.

The pilot answers three questions with measurements. Does the form lose
a fact that a caller can prove today? How many code lines does it remove
and add, once and for each kind? Can a client prove claims about
programs without the step function in the proof?

## Acceptance

### Kind rules

The model has one kind rule for CREATE TABLE and one for plain INSERT.
Each rule meets these conditions:

- Its only premise about the statement syntax is the resolution
  equation. The other inputs are the connection, the clock, the index
  and the parameters.
- It determines the result for every such input: no input is left
  without a conclusion. A premise that selects a case, such as
  `InsertFits`, belongs to a corollary and not to the rule.
- Its conclusion names functions on the database, the table, the rows,
  the counters and the connection (`Connection.afterWrite`,
  `Connection.afterError`). It does not name `runScriptStepWith`,
  `SqlState.statementRun`, `advanceRun` or `Output.ofStep`.

The CREATE TABLE rule says that the step continues exactly when the
target is the end of the catalog and the row stores are aligned with the
catalog. A step that continues has the output of a statement that
changes no rows, a next connection that differs only in the database,
which has the table and an empty row store appended, and no further
execution. In every other case the run ends.

The plain INSERT rule covers the three results: the run ends, the
statement succeeds, and the statement fails. It gives the condition of
each one. The run ends in these cases, and in no other:

- `statementClock` gives `none`: the statement reads the clock and the
  run has no clock.
- `Counters.firstUnknown` finds an unknown counter among the counters
  that the statement reads (`counterReads`).
- The target holds no table.
- The target holds a table, and one of the three readiness checks of the
  run fails: `LiteralData.insertReady`, `Resolved.subqueriesPlain` or
  `Resolved.cellsReady`.

An INSERT that reads no clock and no counter continues without a clock
and with unknown counters. A success has the output `.done rows.length`, the target with
the rows of `LiteralData.inserted`, and the counts of
`LiteralData.insertCounts`. A failure has an error output with the code
of the violation, the database before the statement, and the counts of
the failed insertion. Neither has a further execution.

### Data facts

Each of these facts is a theorem that mentions no step, no resolution
and no connection:

- The table at the end of the catalog after CREATE TABLE has the given
  shape and no rows.
- CREATE TABLE keeps each table that a name finds, at the same position
  with the same rows.

### Generic projections

Each of these facts has one theorem that takes a kind rule, or a
consequence of it, and no premise about the kind. They hold for both
pilot kinds, and their statements do not assume that a step has one
execution:

- The partial form: every fact of the rule about a step that continues,
  from the step equation and the resolution equation alone.
- The step continues, from the conditions of the rule.
- The step has no further execution.
- The output is not a choice between results.
- The output is not an error, for a kind or a case without failure.

### Replaced laws

These laws are deleted, and their callers use the new form. No alias
remains.

- Model: `runScriptStep_createTable`, `runScriptStep_createTable_ok`,
  `runScriptStep_createTable_frame`, `runScriptStep_createTable_empty`,
  `runScriptStep_insert_ok`, `plainInsert_database`,
  `runScriptStep_insert_ne_oneOf`. The last law holds for every INSERT,
  also with a RETURNING clause or write rules. The existing law
  `runScriptStep_ne_oneOf_of_not_query` gives it for every statement
  that is not a query, so its callers use that law.
- Surface: `Sql.check_send_createTable`, `Sql.check_send_plainInsert`,
  `Sql.ifOk_send_plainInsert`.

A law of this list can stay only when the findings record gives the
reason, for example a caller outside the two kinds that needs it
unchanged.

### No capability loss

A test file proves the statement of each replaced law, model and
surface, from the laws that remain, with the premises that the law has
today or with weaker premises. The statements are copied from the
revision before the pilot, with their quantified posts and premises.
This includes the facts that the partial laws give without validity:
`runScriptStep_createTable` derives the two guard facts from the
resolution equation and a step that continues, and
`plainInsert_database` needs only the resolution equation, the table,
the step equation and an output without error.

### Surface

- One theorem connects a kind rule to `Sql.check` of a program that
  sends one statement. It does not depend on the kind.
- `sql_run` proves goals about the two kinds through that theorem.
  `SqlRunRules.lean` has no entry for the two kinds in `sendRule`, and
  no list of binder names for them in `roleOf`.
- The existing tests that use `sql_run` keep their claims. A changed
  proof is counted in the findings record.

### Client claims

A new surface test states and proves claims that a client can write, on
databases with a fixed catalog and arbitrary valid rows:

- An INSERT of a row with a new key succeeds: the output is `.done 1`,
  the table holds the old rows and the new row, `changes()` is 1 and
  `last_insert_rowid()` is the rowid of the row.
- The same INSERT with a key that the table holds fails: the output is
  an error with code 19, the database is the database before, and
  `changes()` is 0.
- A program that creates a table and inserts one row into it succeeds,
  and the new table holds exactly that row.
- One claim of the form "the program preserves a condition on the
  database" for a program with an INSERT, proved with `sql_run`.

No proof in this test names `runScriptStep`, `runScriptStepWith`,
`resolveStatement` or `SqlState.statementRun`.

### Model behavior

The results that the executable model computes do not change:
`just verdict` gives the same verdict as before the pilot, and the
conformance tests pass. A change to a definition of the step function is
allowed only when it computes the same value for every input.

### Findings record

`docs/records/statement-rule-pilot-findings.md` records, for the team:

- Code lines before and after (`scc`, as
  `docs/development/lean-simplification-goal.md` counts them) for each
  package and for the tests, split into lines added once and lines
  added for each kind.
- The number of changed callers and of changed lines in them.
- For each replaced law, the statement lines before and the statement
  lines of the theorem that gives the fact now.
- The elaboration time of the modules that the pilot deletes or
  rewrites, and of the modules that replace them. The owner approved
  the pilot with build time as one of its measures.
- The facts that the new form cannot give, or gives only with stronger
  premises.
- What the next kind costs, as an estimate from the two kinds.

## Tests

- The Lean build of the four packages with `--wfail`.
- The surface tests that compile the callers:
  `tests/surface_schema_script_test.py`,
  `tests/surface_assertion_examples_test.py`,
  `tests/surface_rebuild_test.py`,
  `tests/surface_s6_automation_test.py` and `tests/test_model_package.py`.
- The two new test files of "No capability loss" and "Client claims".
  They are fixtures of the existing surface suites: their roots are
  declared in `tests/surface_fixture_roots.json` in the list of the
  suite that compiles them, and an existing test module with a timeout
  runs them, so the Nix checks own and cache the result as they do for
  the other fixtures.
- At the end of the code changes: `just test-full` and `just verdict`.
- At the end of the task: `just test-nix` and
  `just test-scheduled-checks`, once.

The pilot ends with the findings record and an owner decision. A pull
request follows only after that decision.

## Points to know

**Resolution and step.** `runScriptStepWith` resolves the statement and
runs it in one definition. No function names the part after resolution,
and 18 Lean files of the packages name the definition, among them the
conformance package (`RunPass`). A kind rule needs a place to stand: either the
definition gets a named second part, or the rule is stated with the
resolution equation as a premise. The step logic must exist once.

**Checks that occur twice.** `runScriptStepWith` checks
`Counters.firstUnknown`, and `StatementRun.ready` contains the same
check. `runScriptStep_continued_spec`
(`Programs/Scripts/ScriptRunContinued.lean`) lists what a step that
continues gives; it is the present source of the partial form.

**Partial laws have weaker premises.** `runScriptStep_createTable`
needs no validity: it reads the guard from a step that continues.
`runScriptStep_createTable_ok` gets the guard from validity
(`Resolved.Statement.StepGuards`, `step_guards_hold` in
`ResolvedStepGuards.lean`). A rule in the form "if the guard holds then
…" gives only the second.

**CREATE TABLE output.** No law states the output value of CREATE TABLE
today; callers get `output.isError = false`.

**Plain INSERT.** `insertOutcome` (`Schema/Writes/StatementRun.lean`)
chooses between success, code 20 (`aliasMismatch`) and code 19.
For a target that holds no table, `runStatement`
(`Schema/Dispatch/StatementStep.lean`) gives a ready run with the effect
`.unmodeled`, and the step ends through `Output.ofStep`. For a present
target the run is not ready when `LiteralData.insertReady`,
`Resolved.subqueriesPlain` or `Resolved.cellsReady` fails. Its fourth
check, on the RETURNING expressions, always passes for a plain INSERT.
`LiteralData.insertCounts` gives counts for a failure too, and
`Connection.afterWrite` applies them. `InsertFits` and
`InsertFits.of_valid`, `InsertFits.of_valid_alias`
(`Schema/Writes/LiteralInsertFits.lean`) give the success case.
`plainInsert_database` allows only `subqueries = []`;
`runScriptStep_insert_ok` allows plain subqueries. An INSERT can read
the clock and the counters, so `statementClock` and
`Counters.firstUnknown` are part of its "the run ends" case.

**Laws shared with other kinds.** `runScriptStep_plainWrite_frame` and
`runScriptStep_plainWrite_failed` cover INSERT, UPDATE and DELETE
together. `runScriptStep_effect`, `runScriptStep_others` and
`runScriptStep_ne_oneOf_of_not_query` serve all kinds. They stay for the
kinds outside the pilot.

**Callers.** Model: `TableKeeps.lean` (`runScriptStep_keepsTable`),
`CreatedTables.lean` (`runScriptStep_createdTables`),
`StepContinuesOk.lean`, `CreateSchemaSuccess.lean`,
`SchemaFailureLaws.lean`. Surface: `SchemaStepRules.lean`,
`PlainInsertStepRule.lean`, `Reasoning/PlainInsertEffect.lean`,
`Automation/SqlRunRules.lean`, `Automation/SqlRunGoals.lean`. Tests:
`tests/surface/Schema/Tests/` (`PlainInsertStepCases`,
`AddCustomerClaims`, `CustomerInsertSite`, `GlobalSignupInvariant`,
`SignupInvariantClaims`, `S6AutoAddCustomer`, `SchemaCreateExamples`)
and `tests/surface/Programs/Reasoning/` (`S6AutoSignup`,
`SchemaRuleExamples`).

**`sql_run`.** `sendRule` chooses a rule by the syntax kind, and
`roleOf` holds the binder names of each outcome premise. The outcome
goals receive validity of the next connection from
`Sql.check_send_of_step` (`runScriptStep_valid`). The tactic only
applies theorems, so a wrong choice cannot prove a false goal; the new
path must keep that property.

**Package limits.** The core modules of the model package import `Init`
and `Lean.Meta.Tactic.Simp.RegisterCommand`, and no other module of
`Lean` or `Std` (ADR 0006); only its codec imports `Lean`. The surface
package depends on the model package, the SQL text package and
Plausible. The pilot adds no dependency between packages and no import
of a module outside these limits.

## Not in this task

The other statement kinds, INSERT with RETURNING or write rules, rules
for facts that no law gives today and that the two kind rules do not
need, one form for `Succeeds` and `Sql.check`, and the ADR that decides
on the form for all kinds.
