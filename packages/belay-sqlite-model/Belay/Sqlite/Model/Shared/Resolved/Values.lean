import Belay.Sqlite.Model.Shared.Resolved.Profile
import Belay.Sqlite.Model.Shared.Resolved.Resolved
import Belay.Sqlite.Model.Shared.Values.Arithmetic

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Why an expression has no value: a SQLite prepare error of an expression
({name}`ExprError`, which names no catalog object), or a model restriction with the path
of the node inside the expression. -/
inductive ValueIssue where
  /-- SQLite refuses to prepare the statement. -/
  | prepare (error : ExprError)
  /-- The model does not describe the expression at this path, for the reason of the
  restriction kind. -/
  | restriction (path : List Nat) (kind : RestrictionKind)
  deriving Repr, DecidableEq

end Belay.Sqlite.Model
