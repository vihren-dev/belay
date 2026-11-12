import Belay.Sqlite.Model.Shared.Resolved.Operators

set_option doc.verso true

/-! The comparison and arithmetic operators of SQL, without their rules. The syntax and
the resolved forms name operators; the rules are in {lit}`Comparison` and
{lit}`Arithmetic`. Keeping the operators apart means a change of a rule does not
rebuild the syntax and the catalog. -/

namespace Belay.Sqlite.Model

/-- The keywords of a compound operator, as SQLite writes them in its messages. -/
def CompoundOperator.keywords : CompoundOperator → String
  | .unionAll => "UNION ALL"
  | .union => "UNION"
  | .intersect => "INTERSECT"
  | .except => "EXCEPT"

end Belay.Sqlite.Model
