import Belay.Sqlite.Model.Shared.Resolved.Resolved

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Whether the statement is an INSERT from a query without rules, the one statement whose run can
have alternative executions ({name}`Resolved.Statement.insertSelect`). With rules (a trigger or an
enforced foreign key) the model describes the statement only for one production of the query. -/
def Resolved.Statement.fromQuery : Resolved.Statement → Bool
  | .insertSelect _ _ _ _ _ _ _ none => true
  | .insertSelect _ _ _ _ _ _ _ (some _) => false
  | .createView .. | .createTable .. | .createIndex .. | .createTrigger .. | .addColumn .. | .rewrite _ | .dropColumn .. | .drop .. | .begin
  | .commit | .rollback | .insert .. | .update .. | .upsert .. | .delete .. | .prepareError _ | .query .. | .setting .. => false

end Belay.Sqlite.Model
