import Belay.Sqlite.Resolution.Resolved

set_option doc.verso true

/-! The text of SQLite's prepare errors. Each message fills the format that the
constructor of {name}`Belay.Sqlite.PrepareError` names with its arguments. Names
appear as written in the statement, as SQLite prints them. -/

namespace Belay.Sqlite

/-- SQLite's message for a prepare error, for example {lit}`no such table: t`. -/
def PrepareError.message : PrepareError → String
  | .reservedName name => s!"object name reserved for internal use: {name}"
  | .tableExists name => s!"table {name} already exists"
  | .indexNameUsed name => s!"there is already an index named {name}"
  | .tableNameUsed name => s!"there is already a table named {name}"
  | .indexExists name => s!"index {name} already exists"
  | .tooManyColumns table => s!"too many columns on {table}"
  | .duplicateColumn column => s!"duplicate column name: {column}"
  | .multiplePrimaryKeys table => s!"table \"{table}\" has more than one primary key"
  | .defaultNotConstant column => s!"default value of column [{column}] is not constant"
  | .noSuchTable name => s!"no such table: {name}"
  | .noSuchColumn name => s!"no such column: {name}"
  | .tableHasNoColumn table column => s!"table {table} has no column named {column}"
  | .valueCount table columns values => s!"table {table} has {columns} columns but {values} values were supplied"
  | .valuesForColumns values columns => s!"{values} values for {columns} columns"
  | .valuesDiffer => "all VALUES must have the same number of terms"
  | .tableMayNotBeAltered name => s!"table {name} may not be altered"
  | .tableMayNotBeIndexed name => s!"table {name} may not be indexed"
  | .cannotAddPrimaryKey => "Cannot add a PRIMARY KEY column"
  | .cannotAddUnique => "Cannot add a UNIQUE column"
  | .hexLiteralTooBig text => s!"hex literal too big: {text}"

end Belay.Sqlite
