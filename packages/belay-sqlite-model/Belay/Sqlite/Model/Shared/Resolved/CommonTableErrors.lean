import Belay.Sqlite.Model.Shared.Values.Identifier

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- An invalid WITH definition, with the name as SQLite prints it. For example,
{lit}`WITH c AS (SELECT * FROM c) SELECT * FROM c` has a circular reference. -/
inductive CommonTableError where
  /-- Two definitions in one WITH clause have the same name. -/
  | duplicate (name : Identifier)
  /-- A definition reaches itself outside a permitted recursive term. -/
  | circular (name : Identifier)
  /-- The explicit column list has a different length from the result. -/
  | columns (name : Identifier) (values columns : Nat)
  /-- One recursive term has more than one direct reference to its CTE. -/
  | repeatedTable (name : Identifier)
  /-- A recursive term contains an additional, nested recursive reference. -/
  | repeatedReference (name : Identifier)
  /-- A recursive arm contains an aggregate query. -/
  | recursiveAggregate
  /-- A CTE is called with table-function arguments. -/
  | functionCall (name : Identifier)
  deriving Repr, DecidableEq

end Belay.Sqlite.Model
