import Belay.Sqlite.Model.Shared.Resolved.ViewErrors

set_option doc.verso true

/-! SQLite errors when a query uses a stored view definition. Creation can retain
an unresolved body; these checks happen when a later statement expands it. -/

namespace Belay.Sqlite.Model

/-- The view name carried by an error, for placement of the SQL diagnostic. -/
def ViewError.name : ViewError → Identifier
  | .circular name | .columns name _ _ | .functionCall name => name

/-- SQLite's message for a failed view expansion or a view used as a function. -/
def ViewError.message : ViewError → String
  | .circular name => s!"view {name} is circularly defined"
  | .columns name expected actual => s!"expected {expected} columns for '{name}' but got {actual}"
  | .functionCall name => s!"'{name}' is not a function"

end Belay.Sqlite.Model
