import Belay.Sqlite.Model.Output
import Belay.Sqlite.Model.Connection

set_option doc.verso true

/-! One possible execution of a statement (ADR 0019, D4, amended 2026-10-25; ADR 0012,
clarification of 2026-10-25). A statement can have several admitted results: an index can change
rowids, partial writes and the precedence of errors. Each result is a complete execution with its
own output and its own connection. A later statement runs from the connection of the execution that
reached it, and a part of one execution is never combined with a part of another.
{lit}`ScriptRun.lean` gives the executions of a statement ({lit}`RunStep`), and
{lit}`ScriptRunAll.lean` gives the complete executions of a script. -/

namespace Belay.Sqlite.Model

/-- One possible execution of a statement on a connection: the output that it gives and the
connection that it leaves, with its database, counters, transaction and settings. For example, an
UPDATE that changes one row has one execution, with the output {lean}`Output.done 1`. -/
structure StatementExecution where
  /-- The output of the statement in this execution. It is never {name}`Output.unmodeled`: a
  statement that the model does not describe has no execution. -/
  output : Output
  /-- The connection after the statement in this execution. -/
  next : Connection

/-- The execution that a run of a statement gives, from the values bound to its parameters, the
connection before the statement, the resolved statement, the resolution state {lit}`after` it, its
clock value, its run and the transition of that run: the output {name}`Output.ofStep` and the
connection {name}`Connection.afterStep` with the counts of the run. It is the reason when the output
is {name}`Output.unmodeled`, because such a statement has no execution. -/
def StatementExecution.ofRun (parameters : List Value) (connection : Connection) (resolved : Resolved.Statement)
    (after : ResolveState) (value : Int) (run : StatementRun) (transition : SqlTransition) :
    Except String StatementExecution :=
  match Output.ofStep value parameters resolved connection.state run transition with
  | .unmodeled reason => .error reason
  | output@(.rows _) | output@(.done _) | output@(.error _) | output@(.oneOf _) =>
    .ok { output, next := connection.afterStep after run.counts transition }

/-- A further execution of a statement together with the run and the transition that gave it. A
user of the model that needs more than the output and the connection of an execution, such as the
conformance runner that observes the state after the statement, reads them here. -/
structure StatementExecution.Traced where
  /-- The execution: its output and its connection after the statement. -/
  execution : StatementExecution
  /-- The run of the statement that gave this execution. -/
  run : StatementRun
  /-- The transition of that run on the connection before the statement. -/
  transition : SqlTransition

/-- The further executions of a statement at an index, from the values bound to its parameters, the
connection before the statement, the resolved statement, the resolution state {lit}`after` it, its
clock value and its run: for each alternative of the run ({name}`StatementRun.alternatives`), the
execution that it gives ({name}`StatementExecution.ofRun`), with its run and the transition of
{name}`advanceRun` on the connection before the statement. It is the reason when an alternative has
no output. For a run without alternatives it is the empty list. -/
def StatementExecution.ofAlternatives (index : Nat) (parameters : List Value) (connection : Connection)
    (resolved : Resolved.Statement) (after : ResolveState) (value : Int) (run : StatementRun) :
    Except String (List StatementExecution.Traced) :=
  run.alternatives.mapM fun alternative =>
    let alternativeRun := alternative.toRun
    let transition := advanceRun index resolved connection.state alternativeRun
    (StatementExecution.ofRun parameters connection resolved after value alternativeRun transition).map
      fun execution => { execution, run := alternativeRun, transition }

/-- The executions that an execution with several permitted results stands for: for the output
{name}`Output.oneOf`, one execution with {name}`Output.rows` for each listed result, all with the
same next connection; every other execution stands for itself. This is the correspondence between
the permitted results of a query on one unchanged state and executions that share their next state.
For example, a query with the two permitted results {lit}`[[1]]` and {lit}`[[2]]` stands for two
executions with the outputs {lit}`rows [[1]]` and {lit}`rows [[2]]` and the same connection. -/
def StatementExecution.expand (execution : StatementExecution) : List StatementExecution :=
  match execution.output with
  | .oneOf results => results.map fun rows => { execution with output := .rows rows }
  | .rows _ | .done _ | .error _ | .unmodeled _ => [execution]

end Belay.Sqlite.Model
