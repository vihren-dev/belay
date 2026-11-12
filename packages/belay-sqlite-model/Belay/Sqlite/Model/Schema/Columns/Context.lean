import Belay.Sqlite.Model.Queries.Select.Defaults
import Belay.Sqlite.Model.Schema.Columns.Defaults

set_option doc.verso true

/-! The inputs of statement resolution, the result of one statement, and the
predicates on names and constraints that several statements share. -/

namespace Belay.Sqlite.Model

/-- Whether the model describes a catalog default: a literal whose value or
SQLite preparation error is modeled, or a time keyword such as {lit}`CURRENT_TIMESTAMP`, which is kept
without evaluating it. Compound expressions remain model restrictions. Constraints
without a default pass this check. -/
def Syntax.ColumnConstraint.modeledDefault : Syntax.ColumnConstraint → Bool
  | .default (.currentTime _) _ => true
  | .default expression _ => match literalDefault expression with
    | .ok _ | .error (.prepare _) => true
    | .error (.restriction ..) => false
  | .notNull _ | .primaryKey .. | .unique _ | .collate _ | .check .. | .references .. | .generated .. | .deferral _ => true

end Belay.Sqlite.Model
