import Belay.Sqlite.Model.Shared.Resolved.JsonFunction
import Lean.Expr
import Lean.Level
import Lean.ToExpr

set_option doc.verso true

namespace Belay.Sqlite.Model

deriving instance Lean.ToExpr for Resolved.JsonFunction

end Belay.Sqlite.Model
