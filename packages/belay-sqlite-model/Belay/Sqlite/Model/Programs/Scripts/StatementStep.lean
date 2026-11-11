import Belay.Sqlite.Model.Programs.Clock.StatementClock
import Belay.Sqlite.Model.Schema.Dispatch.StatementStep

set_option doc.verso true

/-! The run of one resolved statement (ADR 0013, D8): its effect, its support check and its
counts. The transitions of script-directed SQL execution, which use it, are in
{lit}`SqlAdvance.lean`. -/
namespace Belay.Sqlite.Model

/-- Whether the model describes the statement with the counters and the values bound to its
parameters on the database ({name}`runStatement`). Use it through the reached-statement script support check. -/
def statementReady (clock : Int) (counters : Counters) (parameters : List Value) (statement : Resolved.Statement) (database : Database) :
    Bool :=
  (runStatement clock counters parameters statement database).ready

end Belay.Sqlite.Model
