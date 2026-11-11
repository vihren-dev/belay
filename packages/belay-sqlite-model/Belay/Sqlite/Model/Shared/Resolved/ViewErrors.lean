import Belay.Sqlite.Model.Shared.Values.Identifier

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- A view-use error, with the declared view name for cycles and column counts,
and the written source name for a function call. These are SQLite errors. -/
inductive ViewError where
  /-- A used definition reaches the same view while it is being expanded. -/
  | circular (name : Identifier)
  /-- The explicit output list has a different length from the resolved body. -/
  | columns (name : Identifier) (expected actual : Nat)
  /-- A view is used with table-function arguments. -/
  | functionCall (name : Identifier)
  deriving Repr, DecidableEq

end Belay.Sqlite.Model
