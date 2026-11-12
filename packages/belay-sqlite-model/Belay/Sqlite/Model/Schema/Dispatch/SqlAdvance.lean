import Belay.Sqlite.Model.Schema.Dispatch.StatementStep
import Belay.Sqlite.Model.Shared.Execution.SqlAdvance

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Evaluate one statement with the values bound to its parameters at its supplied zero-based
position ({name}`advanceRun` of its run at the clock value of the position,
{name}`runStatement`). -/
def advance (position : Nat) (statement : Resolved.Statement) (parameters : List Value) (state : SqlState) :
    SqlTransition :=
  advanceRun position statement state (SqlState.statementRun state (state.clock position) parameters statement)

/-- Execute the script from a supplied position and connection state, each statement with the
values bound to its parameters ({name}`bindValues` binds a list of lists). A halt stops
the script; a continuing transition advances the position. EOF finishes the
current state and preserves an open transaction. The idle wrapper starts at position zero. -/
def runSqlFrom (position : Nat) (script : List (Resolved.Statement × List Value)) (state : SqlState) : Outcome :=
  match script with
  | [] => state.finish (.success state.database)
  | (statement, parameters) :: rest => match advance position statement parameters state with
    | .halt outcome => outcome
    | .next next => runSqlFrom (position + 1) rest next

/-- Execute a resolved script from position zero outside a transaction. Use
{name}`runSqlFrom` for an explicit position/state. A file is not implicitly atomic;
transaction control must be supplied in its statements. -/
def runSql (script : List (Resolved.Statement × List Value)) (database : Database) : Outcome :=
  runSqlFrom 0 script { database := database }

end Belay.Sqlite.Model
