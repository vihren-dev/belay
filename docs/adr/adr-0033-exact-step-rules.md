# ADR 0033: One exact step rule for each statement kind

Date: 2026-11-23. Status: PROPOSED. Owner decision 1 is decided (owner, 2026-11-23: "I accepted
your recommendation. So we will adopt this style for all kinds of sql statements."). Owner
decisions 2 and 3 are open.
Audience: designers and reviewers.
Evidence: the [findings record of the pilot](../records/statement-rule-pilot-findings.md) and its
[task file](../../plans/20261123-statement-rule-pilot.task.md).
Related: issue #468 (the forms of a step law), [ADR 0017](adr-0017-user-surface.md) (the user
surface and `sql_run`), [ADR 0025](adr-0025-compositional-preservation-proofs.md) and
[ADR 0026](adr-0026-semantic-proof-boundaries.md) (the retention witnesses of replaced laws),
[ADR 0027](adr-0027-compositional-select-proofs.md) (the contracts of SELECT), the
[simplification goal](../development/lean-simplification-goal.md).

## Overview

A client of Belay proves claims about programs that send SQL statements. Each claim needs facts
about the step of one statement: when the step continues, its output, and the connection after
it. The model gives these facts as many partial laws for each statement kind. A fact that no law
states is available only to a proof that unfolds the step function.

The owner set the goal for these laws on 2026-11-23: "we want to develop a set of laws which
make all reasonable propositions clients could state provable without unneccesary work. And we
want to avoid code duplication, so we prefer readable, general laws with lots of applications
rather than repeating the same patterns for specific laws again and again".

A pilot compared three forms of such laws on CREATE TABLE and plain INSERT. The owner selected
the first form, the kind rule. This ADR adopts it for all statement kinds:

- **One exact rule for each kind.** The rule has the resolution of the statement as its only
  premise. It gives the step as an equation in which each case is visible: each case that ends
  the run, the success and the failure.
- **Data facts.** A fact that selects a case of a rule, or that describes the result of a case,
  is a theorem about a function on data. It names no step and no resolution.
- **One set of projections and one surface rule for all kinds.** They read facts from the
  equation of a rule. The surface rules that take the resolution to one kind, and the table of
  kinds in `sql_run`, go.

The ADR also gives the order of the work and what each part must show.

## Context

### The step function

`runScriptStep` (`Programs/Scripts/ScriptRun.lean` of the model package) runs one statement on a
connection and gives a `RunStep`: `.continued output next others` or `.ended reason`. It makes
these checks in this order:

1. It resolves the statement (`resolveStatement`). A statement that does not resolve ends the run.
2. It takes the clock value of the statement (`statementClock`). A statement that reads the clock
   in a run without a clock ends the run.
3. It looks for a counter that the statement reads and that the connection does not know
   (`Counters.firstUnknown`). Such a counter ends the run.
4. It runs the statement (`SqlState.statementRun`, which calls `runStatement`). A run that is not
   ready ends the run.
5. It computes the output and the next connection (`Output.ofStep`, `advanceRun`,
   `ranScriptStep`).

`runStatement` (`Schema/Dispatch/StatementStep.lean`) selects the effect, the support check and
the counts by the constructor of `Resolved.Statement`. The type has 19 constructors. Some
arguments of a constructor select a mode. For example, `insert` has the list of RETURNING columns
and the optional write rules of foreign keys and triggers; an INSERT with no RETURNING column and
no write rules is a plain INSERT.

### The laws on main

On main `b7854558`, the start revision of the pilot:

- The model has 99 theorems about `runScriptStep` (count of the pilot task file). Most of them
  state one fact about one kind, with the same two premises: the statement resolves to the kind,
  and the step continued. Issue #468 found at least 40 laws of this shape in 24 files. A law of
  this shape says nothing about the cases in which the step ends.
- The surface has 11 rules `Sql.check_send_<kind>` and 4 rules `Sql.ifOk_send_<kind>`. Each rule
  states the premises of a send again. For example, the rules of plain INSERT, plain UPDATE, plain
  DELETE and ADD COLUMN each have the premises `valid`, `found`, `present`, `modeled`, `success`
  and `failure`.
- `sql_run` selects the surface rule with a table (`sendRule` in
  `Programs/Automation/SqlRunRules.lean`). The table has one branch for each kind with a rule.
  Lists of kinds (`schemaKinds`, `controlKinds`) give the names of the hypotheses of each
  outcome.

A new fact about a kind is thus a new law, and a new kind is a new group of laws, a surface rule
and a table entry.

### The pilot

The pilot replaced the laws of CREATE TABLE and plain INSERT, and measured three forms of the
laws of plain INSERT. All numbers are scc code lines from the findings record. Its last measured
revision is `a03e8267`, which holds the three forms.

| Form | What it is | Model lines for plain INSERT |
| --- | --- | ---: |
| Kind rule | One equation for the step with each case visible; data facts select a case | 84 in the rule file |
| Case laws | One theorem for the success and one for the failure, proved from the kind rule | +52, and 28 for the data facts of a failed insertion |
| Case type | An inductive proposition with one constructor for each case, with theorems for cover and for one result | +146, of which 49 once for all kinds |

Other results of the pilot:

- **No fact lost.** A retention test proves the statement of each replaced law, copied from the
  start revision, with the same premises.
- **Cost that is paid once.** The projections, the simp set `step_rule`, the surface rule
  `Sql.check_send_of_rule` and the path of `sql_run` through the rules add 296 lines. They do not
  depend on the kind.
- **Saving for each kind.** With the deleted laws and the changed callers, the kind rule changes
  the total by −26 lines for CREATE TABLE and by −147 lines for plain INSERT. With the kind
  rules alone, the pilot changed the total by +125 lines at revision `94c3fa5e`, without its
  acceptance tests.
- **Client proofs.** For the two client claims about INSERT, the declarations that differ
  between the forms take 79 lines with the kind rule (at `94c3fa5e`), 75 with the case laws and
  69 with the case type. With the data facts of a failed insertion, the kind rule takes 74
  lines. The claim about each input ("the INSERT has the output `.done 1` and the new row, or
  an error and the database before") takes 40 lines with the kind rule, 57 with the case laws
  and 53 with the case type. No client proof names the step function.
- **Where the client lines are.** The two modules that define the table and the statement of
  the client test and prove their data facts (readiness, fit, keys and counts) have 106 lines
  at `a03e8267`. Site facts of 63 lines have the same code in each form.
- **Elaboration time.** No model or surface module that the pilot changed differs by more than
  0.1 s. One test fixture with two new proofs went from 2.18 s to 5.02 s; the other changed
  fixtures differ by less than 0.4 s.

With the same data facts, the 52 lines of the case laws make the two client proofs 1 line
longer (75 against 74), and the 146 lines of the case type make them 5 lines shorter. The proof
of the claim about each input is shortest with the kind rule. The owner selected the kind rule
alone. The pilot task now removes the other two forms and keeps the data facts of a failed
insertion (its section "Owner decision of 2026-11-23"); the findings record keeps the
measurements.

### What the pilot did not test

- A step with further executions (`others` is not empty) or with an output that is a choice
  between results. `Sql.check_send_of_rule` allows both, but the two pilot kinds have neither.
  On main, the output of a query can be a choice, and the general rules for a send exclude
  INSERT from a query (`Sql.check_send_of_step_notInsertSelect`).
- A kind with write rules (foreign keys, triggers) or with RETURNING columns.
- More than two rules in the set `step_rule`. `sql_run` tries the rules in the order of their
  names until the resolution premise of one closes.

## Decision

In this ADR, a *kind* is a constructor of `Resolved.Statement` with fixed values for the
arguments that select a mode. Plain INSERT is the kind `.insert target rows [] subqueries none`.

### D1. The kind rule

Each kind has one theorem, its kind rule, with the name `runScriptStep_<kind>_eq` and the
attribute `@[step_rule]`:

```lean
@[step_rule] theorem runScriptStep_createTable_eq
    (found : resolveStatement context connection.resolveState statement =
      .ok (.createTable target name table, after)) :
    runScriptStep context clock index connection statement parameters =
      if target = connection.state.database.catalog.length ∧
          connection.state.database.rows.length = connection.state.database.catalog.length then
        .continued (.done 0) (connection.withDatabase (connection.state.database.createTable name table)) []
      else .ended unmodeledHere
```

- The resolution equation is the only premise. The rule has no premise about validity, about the
  clock, or about a step that continued.
- The conclusion is an equation for the step. It holds for each connection, clock, index and
  list of parameter values.
- The kind rule is the only theorem about the kind whose proof unfolds the step function. Each
  other fact about the step of the kind follows from the rule.

### D2. Kinds are disjoint and cover each constructor

- Two kind rules do not apply to the same resolved statement. When a constructor has more than
  one kind, the patterns of the kinds differ in a mode argument, for example `none` and
  `some rules`.
- A kind fixes a mode argument only when the fixed value makes the right side of the rule
  simpler. An argument that the step uses in the same way for each value stays a variable.
- The kinds of one constructor together cover the constructor, subject to owner decision 2.

### D3. The right side of a rule

- Each case is visible in the term: each case in which the run ends, with its reason, and each
  case in which the step continues, with its output, its next connection and its further
  executions.
- The cases have the order of the checks of the step function. A check that the kind passes for
  each input does not appear. For example, the rule of CREATE TABLE has no case for the clock and
  none for the counters.
- The term names the functions on data that compute the cases, for example
  `Database.createTable`, `LiteralData.inserted`, `insertOutcome` and `Connection.afterWrite`. It
  does not name the functions that select by the kind or that hide the cases: `runStatement`,
  `SqlState.statementRun`, `advanceRun`, `Output.ofStep` and `ranScriptStep`. `statementClock`
  and `Resolved.Statement.counterReads` can appear, applied to the pattern of the kind.
- When a part of the result has no function on data with a name, the slice gives it one in the
  model, as the pilot did with `Database.createTable`. The definition of the step function does
  not change.
- The docstring of the rule states each case in plain words, in the order of the term.

### D4. Data facts

A data fact is a theorem about the functions that a rule names. It has no step, no resolution
and no connection in its statement. Examples from the pilot:

- `insertReady_of_fits` and `insertOutcome_of_fits`: rows that fit the table pass the support
  check of the table and the values, and give a successful outcome. With the subquery check and
  the cell check of the rule, they select the success case.
- `insertOutcome_constraintViolation`: when no supplied row has an alias cell that SQLite
  refuses, a result that repeats a rowid or violates a constraint of the keys gives the outcome
  "constraint violation" with the database before. It selects the failure case.
- `Database.table_createTable_end`: in a database with one row list for each catalog object,
  the new table is at the position after the catalog before and has no rows. It describes the
  result of a case.

When more than one caller needs the same consequence of a case, the consequence is a data fact.
It is not a law about the step of the kind.

### D5. Laws for all kinds

- The projections of `Programs/Scripts/StepRuleProjections.lean` read a fact about the step from
  the equation of a rule: `RunStep.of_rule` (the partial form, for a step that continued),
  `RunStep.continued_of_rule`, `RunStep.continues_of_rule`, `RunStep.Continuing` and
  `RunStep.continuing_ite`. They do not depend on the kind. A slice adds a projection only when
  it serves the rules of more than one kind.
- The laws that hold for each statement kind stay as they are, for example
  `runScriptStep_valid`, `runScriptStep_effect`, `runScriptStep_resolved`, `step_guards_hold`,
  `runScriptStep_counters` and `runScriptStep_index`. A kind rule does not replace them.
- A law for a group of kinds stays with its statement while a kind of the group has no rule.
  For example, `runScriptStep_plainWrite_frame` and `runScriptStep_plainWrite_failed` hold for
  each INSERT, UPDATE and DELETE without write rules (`Resolved.Statement.plainWriteTarget`),
  with or without RETURNING columns. The slice that gives the last kind of the group its rule
  keeps the law when callers use it for more than one kind.

### D6. One surface rule and one path of `sql_run`

- `Sql.check_send_of_rule` is the surface rule for the send of one statement through a kind
  rule. Its premises are the equation of the rule, the validity of the connection, `modeled`
  (the result continues) and `reached` (each continuing case gives the post). It has no premise
  about the kind.
- A slice deletes the surface rules of its kinds that have the resolution to the kind as a
  premise (`Sql.check_send_<kind>` and `Sql.ifOk_send_<kind>` with the premise `found`), and
  the branch of `sendRule` for them. The slice that moves the last kind deletes `sendRule` and
  the parts of `roleOf` and of the lists of kinds that only `sendRule` uses. `roleOf` also
  serves the read path of `sql_run` (`query` and `single`); that part stays.
- `sql_run` finds the kind rules in the set `step_rule`. A new kind rule needs no change of the
  tactic.
- Today, the path of `sql_run` through the kind rules splits the cases of a rule. It does not
  enter the further executions of a case or the results of an output that is a choice. The
  first slice whose kind has one of the two extends the path, so that `sql_run` enters each
  execution and each result as it does for a sent SELECT today.
- `Sql.check_exec` stays. It is the exact rule for one executed statement, and it needs no kind
  rule. The kind rules are thus not the only way to a fact about a send.
- The general rules for a send without a kind rule (`Sql.check_send_of_step`,
  `Sql.check_send_of_step_notInsertSelect`) stay while a kind has no rule. The slice that removes
  the last caller of one of them deletes it.

### D7. No other maintained form

The repository does not keep these forms for a kind that has a rule:

- A partial law of the kind: "if the statement resolves to the kind and the step continued,
  then …". `RunStep.of_rule` gives each such fact from the rule. A law for a group of kinds is
  not such a law (D5).
- Case laws: one theorem for one case of the rule.
- A case type: an inductive proposition over the cases, with cover and one result.
- The named forms of issue #468 for a step of one kind: the bundle `ContinuedStep`, the
  propositions `RunStep.ContinuesOnce` and `RunStep.SucceedsOnce`, and a Hoare triple on one
  model statement.

The triples on programs (`Sql.check`, `Std.Do.Triple` on `Sql`) do not change: the surface rule
of D6 gives the check of a send, and the program rules compose it.

### D8. Replaced laws and retention

- A slice deletes each law that the rule and the data facts replace, and updates each caller.
  It keeps no alias and no second path.
- The slice has a retention test. For each deleted law, the test states the law as it was at the
  start revision of the slice, with the same premises, and proves it from the new laws. This is
  the evidence that the original claims stay derivable, which the simplification goal asks for.
- When a slice cannot prove a deleted statement with the same premises, the work stops and the
  owner decides.
- How long the retention tests stay is owner decision 3.

### D9. Client claims

Each slice shows that a client can use its rules:

- For each kind of the slice, a surface test proves at least one claim about a program that sends
  a statement of the kind to a database that is a variable with stated properties, not a
  concrete database. An existing test that the slice updates counts. For a kind that can fail,
  one claim is about the failure, or about each input.
- No proof of these claims names `runScriptStep`, `runScriptStepWith`, `resolveStatement` or
  `SqlState.statementRun`.
- The data facts that these proofs need and that are not specific to the test go into the model
  (D4).

### D10. Slices

Each slice has its own task file and status file. The pilot is slice 1. The order puts the kinds
with the most callers first.

| Slice | Kinds | Notes |
| --- | --- | --- |
| 1 | CREATE TABLE, plain INSERT | The pilot. |
| 2 | Plain UPDATE, plain DELETE | Deletes `Sql.check_send_plainUpdate`, `Sql.check_send_plainDelete` and their `ifOk` rules. The laws for the group of the plain writes stay (D5). |
| 3 | BEGIN, COMMIT, ROLLBACK, a pragma that sets a value | Deletes `Sql.check_send_begin`, `Sql.check_send_commit` and `Sql.check_send_setting`. ROLLBACK has no step law and no surface rule today. |
| 4 | CREATE INDEX, CREATE VIEW, CREATE TRIGGER, ADD COLUMN, DROP without write rules, the catalog rewrite of a rename, DROP COLUMN, a statement that SQLite refuses to prepare | Deletes `Sql.check_send_addColumn`, `Sql.ifOk_send_addColumn`, `Sql.check_send_dropPlain` and `Sql.check_send_rewrite`. |
| 5 | A query | The first kind whose output can be a choice between results (D6). The contracts of ADR 0027 do not change. See the note on `Sql.check_send_select` below. |
| 6 | INSERT with conflict clauses or a conflict algorithm, INSERT from a query, both without write rules and RETURNING | Row-by-row writes. The general rules for a send exclude INSERT from a query today. |
| 7 | The kinds with write rules, and the kinds with RETURNING columns | Subject to owner decision 2. |

`Sql.check_send_select` is not a rule of the form that D6 deletes. Its premise is the syntax of a
SELECT, not a resolution, and it has no premise about validity. It thus holds for a context
that is not valid and for a SELECT that SQLite refuses to prepare, where the surface rule of D6
does not apply. Slice 5 deletes it only when both of these hold: the retention test proves it
with its premises (D8), and `sql_run` enters each result of a choice through the kind rules
(D6). If not, the rule and its branch of `sendRule` stay, and the status file of the slice
records the reason. The rules for the programs `query` and `single` (`Sql.check_query_select`,
`Sql.check_single_select`) are not rules for a send, and this ADR does not change them.

### D11. What each slice records

The status file of a slice records, for its start and end revisions:

- The code lines of the packages and of the tests, with the counter and the file selection of
  the simplification goal.
- The list of the replaced laws and of the deleted surface rules.
- The elaboration time of each test fixture that uses `sql_run` and that the slice changes, at
  the two revisions.
- The capability groups of the simplification goal that the replaced laws belong to, with the
  retention test as their evidence.

A slice changes no definition that the step function uses, except to give a name to an existing
term (D3). Its end checks therefore include that the verdict files are the same as at its start
revision. The last slice adds a milestone row to the simplification goal.

## Consequences

- **A client can prove each fact about the step of a kind.** The rule is exact, so a fact that
  holds for the step follows from the rule and from facts about data. Outputs, counts and the
  cases that end the run, which most partial laws do not state, are in the rule.
- **A new kind costs one rule and its data facts.** In the pilot, a rule file has 30 lines for a
  kind without data (CREATE TABLE) and 84 lines for a write (plain INSERT). The kind needs no
  surface rule and no change of `sql_run`.
- **A rule is longer than each law that it replaces.** The rule of plain INSERT has 30 statement
  lines. A reader sees the whole step of the kind in one place, in the order of its checks.
- **The saving in lines is small, and the total can grow.** The pilot saved 26 and 147 lines
  for its two kinds after a cost of 296 lines that is paid once. A rough subtotal for the other
  kinds: nine kinds have surface rules of their own today; in the range of the pilot, they save
  about 230 to 1,300 lines. ROLLBACK and the kinds of slices 6 and 7, about ten kinds, have few
  laws of their own to delete; at 30 to 84 lines for a rule file, they add about 300 to 840
  lines. The subtotal does not include the five kinds of slice 4 without a surface rule of
  their own (CREATE INDEX, CREATE VIEW, CREATE TRIGGER, DROP COLUMN, a statement that SQLite
  refuses to prepare), the client tests of D9 (239 lines for plain INSERT in the pilot) and
  the retention tests while they stay. The best case of the subtotal is a saving of about
  1,000 lines, which is about 1% of the 97,505 lines at `b7854558`. This ADR is not a step to
  the 45,000 lines of the simplification goal. Its value is in the first two consequences, and
  in the laws that later facts and kinds do not need.
- **`sql_run` proofs change at the goals of a send.** A proof that names the cases `success` and
  `failure` of a kind's rule gets the goals `modeled` and the cases of the rule. The pilot
  changed four such proofs.
- **Risks.**
  - The right side of a rule for a row-by-row write or for a query can be long. D3 limits it to
    functions on data with names; a slice adds names where the term has none.
  - `sql_run` tries each rule of `step_rule` in turn. With about 20 rules this can cost
    elaboration time. D11 records the time. When the time of a fixture becomes two times as
    long or more, the record of the slice names the proof that causes it.
  - The client still writes the data facts of its tables and statements (106 of 239 lines in
    the pilot). This ADR does not make them shorter.

## Alternatives considered

- **Keep the partial laws.** No change, and no proof obligation for the cases that a client
  does not use. Rejected: each new fact is a new law, the outputs and the ending cases stay
  unstated, and each kind keeps a surface rule and a table entry.
- **Case laws on top of the rule.** A client proof of one case is 4 lines shorter. Rejected: +80
  lines for one kind, and no theorem says that the case laws cover each input.
- **A case type on top of the rule.** It states the partition of the inputs as a type and gives
  the rule back. Rejected: +146 lines, 97 of them for each write kind, for 10 lines in two client
  proofs; the proof of the claim about each input is shorter with the rule (40 lines against
  53).
- **The forms of issue #468.** `ContinuedStep` and `RunStep.ContinuesOnce` give a name to the
  premises of a partial law. They make the statements shorter but keep one law for each fact.
  The Hoare triple on one statement states the success from validity and resolution, which the
  rule and a data fact give, and it does not state the failure or the ending cases.
- **Lean's `fun_cases` for the step function.** Tried in the pilot: it gives five cases without
  names for the checks of the step function, does not split the checks of a kind, and gives no
  theorem that a later proof can use.
- **A step function that makes each rule hold by definition.** The step function would select by
  the kind first, so that a rule is `rfl`. Rejected: the definition is the model that the
  conformance evidence and the mutation tests check, and the proof of a rule is written once.

## Not decided here

- **Shorter data facts for the client.** Laws that give readiness and fit from the validity of
  the database and the types of the values would shorten the 106 lines of the pilot's client
  test. `InsertFits.of_valid` is a first law of this kind.
- **A name for the two first checks.** The rules of the kinds that read the clock or a counter
  start with the same two cases. Slice 2 writes them out, as the pilot does.
- **The data facts of write rules.** A rule for a kind with write rules names `insertKeys`,
  `updateKeys`, `deleteKeys` or `dropKeys`. Laws about these functions are not in this ADR.

## Owner decisions

1. **The form.** Options: (a) the kind rule with data facts and projections for all kinds;
   (b) the kind rule with case laws; (c) the kind rule with a case type; (d) the partial laws
   of main. Recommendation: (a). **DECIDED 2026-11-23: (a).**
2. **The kinds without a surface rule today.** ROLLBACK and the kinds of slices 6 and 7 have no
   surface rule of their own, and ROLLBACK has no step law. Options:
   (a) each kind gets a rule, in the order of D10; slice 7 starts with one kind, INSERT with
   write rules, and records its cost before the other kinds; (b) slices 2 to 6 only, and a rule
   for a kind of slice 7 when a client claim needs it. With (b), `sendRule` keeps its general
   branch (`Sql.check_send_of_step_notInsertSelect`) for the kinds of slice 7 other than INSERT
   from a query, and `Sql.check_exec` is the rule for INSERT from a query with write rules or
   RETURNING columns. Recommendation: (a). It gives `sql_run` one path and each statement an
   exact step, and the record after the first kind of slice 7 lets the owner stop there.
3. **The retention tests.** Options: (a) the rules of ADR 0025 (D4) and ADR 0026 for temporary
   witnesses apply: a retention test stays through the last slice that changes the rule, the
   projections or the surface rule that its proofs use; the status file records the Nix
   acceptance of that final revision; then the test is deleted. A witness that is the only
   check of a premise or of a distinction between cases stays until a caller or a focused test
   covers it. An example is a partial law that needs no validity. (b) The retention tests stay
   in the test suite with no end. Recommendation: (a). At `a03e8267`, the pilot's test has 212
   lines for nine laws, and the tests of the next slices are of the same kind.
