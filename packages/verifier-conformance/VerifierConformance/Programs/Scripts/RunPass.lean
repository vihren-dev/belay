import VerifierConformance.Programs.Scripts.Trace
import Belay.Sqlite.Model.Programs.Scripts.ScriptRun

set_option doc.verso true

namespace Belay.Sqlite.Model.Conformance

/-- The observation after a statement at a zero-based index: the visible and committed
databases and the transaction status of the connection after it, and the error with which its
transition stops ({name}`haltError`), at the index. -/
def observeStep (index : Nat) (next : Connection) (transition : SqlTransition) : Observation :=
  { observeState next.state with error := (haltError transition).map ((index, ·)) }

/-- One possible execution of a statement, as the pass keeps it: the connection after the statement,
the observation, counters, output and possible results after it, and the output of the run
({name}`Output`). -/
structure ExecutionPass where
  /-- The connection after the statement in this execution. -/
  next : Connection
  /-- The observation after the statement ({name}`observeStep`). -/
  observation : Observation
  /-- The writer counters after the statement. -/
  counters : Counters
  /-- The output of the statement ({name}`statementOutput`). -/
  output : Option StatementOutput
  /-- The results that SQLite may give for the statement ({name}`possibleOutput`). -/
  possible : Option (List (List ResultRow))
  /-- The output of the statement in the run ({name}`Output`). -/
  result : Output

/-- The entry of one execution of a statement at a zero-based index on the connection, from the
values bound to its parameters, the resolved statement, its clock value, the execution and the run
and transition that gave it. -/
def ExecutionPass.ofExecution (index : Nat) (parameters : List Value) (connection : Connection)
    (resolved : Resolved.Statement) (value : Int) (execution : StatementExecution) (run : StatementRun)
    (transition : SqlTransition) : ExecutionPass :=
  { next := execution.next, observation := observeStep index execution.next transition,
    counters := execution.next.state.counters,
    output := statementOutput value parameters resolved connection.state run transition,
    possible := possibleOutput value parameters resolved connection.state transition,
    result := execution.output }

end Belay.Sqlite.Model.Conformance
