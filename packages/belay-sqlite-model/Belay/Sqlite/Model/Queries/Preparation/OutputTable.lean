import Belay.Sqlite.Model.Shared.Execution.ScriptRun

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The names of the result columns of the statement: those of a query, and those of the
{lit}`RETURNING` clause of a write; none for another statement. -/
def Resolved.Statement.resultNames : Resolved.Statement → List String
  | .query resolved _ => resolved.names
  | .insert _ _ returning .. | .update _ _ _ returning .. | .upsert _ _ _ returning .. | .insertSelect _ _ _ _ returning .. | .delete _ _ returning .. =>
    returning.map (·.2)
  | .createTable .. | .createView .. | .createIndex .. | .createTrigger .. | .addColumn .. | .rewrite _ | .dropColumn .. | .drop .. | .begin | .commit | .rollback
  | .prepareError _ | .setting .. => []

end Belay.Sqlite.Model
