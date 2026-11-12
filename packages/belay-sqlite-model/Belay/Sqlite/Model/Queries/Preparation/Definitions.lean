import Belay.Sqlite.Model.Values.Scalar.ReadDefaults
import Belay.Sqlite.Model.Queries.Preparation.IndexTerms
import Belay.Sqlite.Model.Queries.Preparation.SpelledNames

set_option doc.verso true

namespace Belay.Sqlite.Model
/-- The positions of key columns, or {lit}`no such column: %s` for the first name
that no column has. -/
def keyPositions (columns : List CatalogColumn) : List Identifier → Except ExprError (List Nat)
  | [] => .ok []
  | name :: rest => match columnPosition columns name with
    | some position => (keyPositions columns rest).map (position :: ·)
    | none => .error (.noSuchColumn name)

/-- Apply the function to the last element of a list; an empty list stays empty. -/
def updateLast (items : List α) (change : α → α) : List α :=
  match items with
  | [] => []
  | [last] => [change last]
  | first :: rest => first :: updateLast rest change

end Belay.Sqlite.Model
