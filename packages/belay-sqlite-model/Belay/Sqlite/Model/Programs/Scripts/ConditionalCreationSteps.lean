import Belay.Sqlite.Model.Programs.StatementRunLaws.CreateIndexSuccessLaws
import Belay.Sqlite.Model.Programs.Scripts.CatalogChangeRules
import Belay.Sqlite.Model.Schema.Ddl.DropTableResolution
import Belay.Sqlite.Model.Programs.Scripts.FailedStepFrame
import Belay.Sqlite.Model.Schema.Ddl.TableByName
import Belay.Sqlite.Model.Schema.Ddl.ConditionalCreationSteps

set_option doc.verso true

/-! Steps at equal resolutions have the same behavior on a connection. -/

namespace Belay.Sqlite.Model

/-- For every context, clock, statement index, connection, bound values and two statements
that resolve to the same result on the connection, one step of each is the same. Proof
sketch: a step reads its statement only through {name}`resolveStatement`. -/
theorem runScriptStep_congr_resolve {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {first second : Syntax.Statement} {parameters : List Value}
    (same : resolveStatement context connection.resolveState first =
      resolveStatement context connection.resolveState second) :
    runScriptStep context clock index connection first parameters =
      runScriptStep context clock index connection second parameters := by
  simp only [runScriptStep, runScriptStepWith, same]

end Belay.Sqlite.Model
