import Belay.Sqlite.Model.StatementExecution
import Belay.Sqlite.Model.Resolution.Resolve
import Belay.Sqlite.Model.SqlExecution

set_option doc.verso true

/-! A run of statement syntax that continues after an error (ADR 0017, D3, amended
2026-10-22). It resolves each statement when it runs, against the state of the connection at
that time: the catalog of the visible database, the catalog at {lit}`BEGIN` of an open
transaction, and the settings of {lit}`PRAGMA foreign_keys` and {lit}`PRAGMA recursive_triggers`.
It runs the statement with
{name}`Belay.Sqlite.Model.runStatement` and {name}`Belay.Sqlite.Model.advanceRun`, gives its
{name}`Belay.Sqlite.Model.Output`, and goes on with the next statement after an error, as an
application that sends one statement at a time does. The run takes an optional clock: a
statement that reads the clock runs with the clock's value at its index, or ends the run when
the run has no clock. A statement that the model does not describe ends the run.

A statement has one or more possible executions ({name}`Belay.Sqlite.Model.StatementExecution`).
The step of a statement ({lit}`RunStep`) lists them, with the execution of the
model's own traversal first. {lit}`runScriptFrom` goes on with that execution;
{lit}`ScriptRunAll.lean` goes on with each one. {lit}`ScriptRunLaws.lean` relates the run to
{name}`Belay.Sqlite.Model.runSqlFrom`. -/

namespace Belay.Sqlite.Model

/-- The reason of a statement that reads the clock in a run without a clock. -/
def clockUnmodeled : String :=
  "the statement reads the clock, which this run does not describe; write the time as a literal value"

/-- The reason of a statement that calls a counter function that the connection does not know
(ADR 0024, D2): it names the function and says how to make the value known. -/
def counterUnknownReason (kind : CounterKind) : String :=
  let function := match kind with
    | .changes => "changes()"
    | .totalChanges => "total_changes()"
    | .lastInsertRowid => "last_insert_rowid()"
  s!"the statement calls {function}, whose value on this connection the run does not know; start the run on a new connection"

/-- The clock value with which a resolved statement at a zero-based index runs: the value of
the clock at the index for a statement that reads the clock
({name}`Resolved.Statement.readsClock`), and 0 for every other statement, as
{name}`scriptClock` gives it. It is {lean}`(none : Option Int)` for a statement that reads the
clock in a run without a clock. Use {lean}`(none : Option Clock)` as the clock when the run
must not read one. -/
def statementClock (clock : Option Clock) (index : Nat) (statement : Resolved.Statement) : Option Int :=
  if statement.readsClock then clock.map (· index) else some 0

/-- What one statement of a run gives: its possible executions, or the reason why the run ends at
it. The first execution is the one that the model's own traversal takes, given as its output and
connection; the others are the further executions that the model admits ({lit}`others`, none for
every statement that the model describes today). -/
inductive RunStep where
  /-- The statement ran, with the output and connection of the model's own execution, which is
  not {name}`Output.unmodeled`, and the other possible executions. -/
  | continued (output : Output) (next : Connection) (others : List StatementExecution)
  /-- The model does not describe the statement; the run ends. -/
  | ended (reason : String)

/-- All possible executions of the step, the model's own execution first; none for a step that
ends the run. -/
def RunStep.executions : RunStep → List StatementExecution
  | .continued output next others => { output, next } :: others
  | .ended _ => []

/-- The step of a statement that ran: it continues with the execution of the model's own
traversal and the others, or ends the run with the reason when an execution has no output. -/
def RunStep.withOthers (output : Output) (next : Connection) : Except String (List StatementExecution) → RunStep
  | .ok others => .continued output next others
  | .error reason => .ended reason

/-- The step of a statement that ran on the connection at an index with the values bound to its
parameters, as resolved, with the resolution state {lit}`after` it, its clock value, its run and its
transition: {name}`Output.ofStep` with the values; an output {name}`Output.unmodeled` ends the run,
and every other output continues with {name}`Connection.afterStep` of the transition and the counts
of the run. Each further execution of the run ({name}`StatementRun.alternatives`) advances from the
same connection with its own effect and counts ({name}`StatementExecution.ofAlternatives`), and one
that has no output ends the run. -/
def ranScriptStep (index : Nat) (parameters : List Value) (connection : Connection) (resolved : Resolved.Statement)
    (after : ResolveState) (value : Int) (run : StatementRun) (transition : SqlTransition) : RunStep :=
  match Output.ofStep value parameters resolved connection.state run transition with
  | .unmodeled reason => .ended reason
  | output@(.rows _) | output@(.done _) | output@(.error _) | output@(.oneOf _) =>
    .withOthers output (connection.afterStep after run.counts transition)
      ((StatementExecution.ofAlternatives index parameters connection resolved after value run).map
        (List.map StatementExecution.Traced.execution))

/-- The steps of one statement of a run up to its transition, with the value to give when the
run ends at the statement ({lit}`ended`, with the reason) and when the statement runs
({lit}`ran`, with the resolved statement, the resolution state after it,
its clock value, its run and its transition). {lit}`runScriptStep` is this function with
{name}`RunStep.ended` and {name}`ranScriptStep`. A caller that needs more of a step than its
output, such as its transition, gives its own values and takes the same steps:

* resolve the statement against {name}`Connection.resolveState`; a restriction ends the run with
  its reason ({name}`NodeRestriction.reason`);
* take its clock value ({name}`statementClock`); a statement that reads the clock in a run
  without a clock ends the run with {name}`clockUnmodeled`;
* take the first counter that the statement reads and the connection does not know
  ({name}`Counters.firstUnknown`); the run ends with {name}`counterUnknownReason`;
* run it with the values at the clock value ({name}`SqlState.statementRun`); a statement that fails
  the support check ends the run with {name}`unmodeledHere`;
* otherwise give {lit}`ran` of the transition of {name}`advanceRun` at the index. -/
def runScriptStepWith {α : Type} (ended : String → α) (ran : Resolved.Statement → ResolveState → Int → StatementRun → SqlTransition → α)
    (context : ResolveContext) (clock : Option Clock) (index : Nat) (connection : Connection)
    (statement : Syntax.Statement) (parameters : List Value) : α :=
  match resolveStatement context connection.resolveState statement with
  | .error restriction => ended restriction.reason
  | .ok (resolved, after) =>
    match statementClock clock index resolved with
    | none => ended clockUnmodeled
    | some value => match connection.state.counters.firstUnknown resolved.counterReads with
      | some kind => ended (counterUnknownReason kind)
      | none =>
        let run := connection.state.statementRun value parameters resolved
        if !run.ready then ended unmodeledHere
        else ran resolved after value run (advanceRun index resolved connection.state run)

/-- Run one statement with the values bound to its parameters at its zero-based index on the
connection, with an optional clock: the steps of {name}`runScriptStepWith`, then
{name}`ranScriptStep` for a statement that runs. A restriction, a statement that reads the
clock in a run without a clock, a statement that reads an unknown counter, a statement that
fails the support check, and an output {name}`Output.unmodeled` end the run. -/
def runScriptStep (context : ResolveContext) (clock : Option Clock) (index : Nat) (connection : Connection)
    (statement : Syntax.Statement) (parameters : List Value) : RunStep :=
  runScriptStepWith .ended (ranScriptStep index parameters connection) context clock index connection statement parameters

/-- The result of a run: the output of each statement that ran, in order, and the connection
at the end. -/
structure ScriptRun where
  /-- One output for each statement that ran; the last is {name}`Output.unmodeled` when the
  run ended early. -/
  outputs : List Output
  /-- The connection after the last statement that ran, or at the start of the statement
  that ended the run. -/
  connection : Connection

/-- Run statements in order, each with the values bound to its parameters, from a zero-based
index on the connection, with an optional clock for each index ({name}`runScriptStep`): the
run goes on after an error and ends at a statement that the model does not describe, whose
output is {name}`Output.unmodeled`. With {lean}`(none : Option Clock)`, a statement that reads
the clock ends the run. -/
def runScriptFrom (context : ResolveContext) (clock : Option Clock) (index : Nat) (connection : Connection) :
    List (Syntax.Statement × List Value) → ScriptRun
  | [] => { outputs := [], connection }
  | (statement, parameters) :: rest => match runScriptStep context clock index connection statement parameters with
    | .ended reason => { outputs := [.unmodeled reason], connection }
    | .continued output next _ =>
      let later := runScriptFrom context clock (index + 1) next rest
      { later with outputs := output :: later.outputs }

end Belay.Sqlite.Model
