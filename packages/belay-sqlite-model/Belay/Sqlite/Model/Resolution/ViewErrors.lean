import Belay.Sqlite.Model.Identifier

set_option doc.verso true

/-! SQLite errors when a query uses a stored view definition. Creation can retain
an unresolved body; these checks happen when a later statement expands it. -/

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

/-- The view name carried by an error, for placement of the SQL diagnostic. -/
def ViewError.name : ViewError → Identifier
  | .circular name | .columns name _ _ | .functionCall name => name

/-- SQLite's message for a failed view expansion or a view used as a function. -/
def ViewError.message : ViewError → String
  | .circular name => s!"view {name} is circularly defined"
  | .columns name expected actual => s!"expected {expected} columns for '{name}' but got {actual}"
  | .functionCall name => s!"'{name}' is not a function"

end Belay.Sqlite.Model
