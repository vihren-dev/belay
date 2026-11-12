import Belay.Sqlite.Model.Shared.Resolved.CommonTableErrors

set_option doc.verso true

/-! SQLite preparation errors specific to WITH definitions. These are SQL errors;
valid recursive queries instead reach the model's recursion restriction. -/

namespace Belay.Sqlite.Model

/-- The CTE name in an error, for placement of its diagnostic in SQL text.
The recursive-aggregate error has no named operand and returns none. -/
def CommonTableError.name : CommonTableError → Option Identifier
  | .duplicate name | .circular name | .columns name _ _ | .repeatedTable name
  | .repeatedReference name | .functionCall name => some name
  | .recursiveAggregate => none

/-- The message SQLite gives for an invalid WITH definition. -/
def CommonTableError.message : CommonTableError → String
  | .duplicate name => s!"duplicate WITH table name: {name}"
  | .circular name => s!"circular reference: {name}"
  | .columns name values count => s!"table {name} has {values} values for {count} columns"
  | .repeatedTable name => s!"multiple references to recursive table: {name}"
  | .repeatedReference name => s!"multiple recursive references: {name}"
  | .recursiveAggregate => "recursive aggregate queries not supported"
  | .functionCall name => s!"'{name}' is not a function"

end Belay.Sqlite.Model
