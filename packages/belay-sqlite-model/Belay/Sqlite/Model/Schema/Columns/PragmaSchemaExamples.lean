import Belay.Sqlite.Model.Schema.Dispatch.Examples
import Belay.Sqlite.Model.Queries.Select.PragmaSchemaExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.PragmaSchemaExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- A column with a declared type and constraints. -/
def typed (text : String) (declaredType : Option String) (constraints : List ColumnConstraint := []) :
    ColumnDefinition :=
  { name := .ofString text, declaredType, constraints }

/-- A text value. -/
def textValue (text : String) : Value := .text text.toUTF8.toList

/-- A name as written, without quotes. -/
def name (text : String) : Expr := .identifier (.ofString text) .none

/-- {lit}`CREATE TABLE t(a INTEGER PRIMARY KEY, b "x""y" NOT NULL DEFAULT 'q', g AS (a + 1), c int
DEFAULT (5), d DEFAULT null)`: a rowid alias, a quoted type, a generated column, a standard
type in lower case, a default in parentheses and {lit}`DEFAULT null`. -/
def createT : Syntax.Statement :=
  .createTable (name! "t") [typed "a" (some "INTEGER") [.primaryKey false],
    typed "b" (some "x\"y") [.notNull, .default (.string "q".toUTF8.toList) "'q'"],
    typed "g" none [.generated (.arithmetic .add (name "a") (.numeric "1")) none],
    typed "c" (some "int") [.default (.numeric "5") "5"], typed "d" none [.default .null "null"]] []

/-- {lit}`CREATE TABLE w(a, b, PRIMARY KEY(b, a)) WITHOUT ROWID`. -/
def createW : Syntax.Statement :=
  .createTable (name! "w") [typed "a" none, typed "b" none] [.primaryKey [name! "b", name! "a"]] { withoutRowid := true }

/-- {lit}`CREATE TABLE c(x REFERENCES p, y, z, FOREIGN KEY (y, z) REFERENCES q(a, b) ON DELETE
CASCADE)`. -/
def createC : Syntax.Statement :=
  .createTable (name! "c") [typed "x" none [.references (name! "p") [] .noAction .noAction], typed "y" none,
    typed "z" none] [.foreignKey [name! "y", name! "z"] (name! "q") [name! "a", name! "b"] .cascade .noAction]

/-- The row of {lit}`PRAGMA foreign_key_list` with the cells after {lit}`id` and {lit}`seq`. -/
def keyRow (id seq : Int) (table source : String) (target : Value) (onDelete : String) : List Value :=
  [.integer id, .integer seq, textValue table, textValue source, target, textValue "NO ACTION", textValue onDelete,
    textValue "NONE"]

/-- The source {lit}`function('argument')`. -/
def pragmaOf (function argument : String) : TableReference :=
  { table := .ofString function, alias := none, arguments := some [.string argument.toUTF8.toList] }

/-- {lit}`SELECT columns FROM function('argument') [WHERE filter]`. -/
def selectFrom (columns : List ResultColumn) (function argument : String) (filter : Option Expr := none) :
    Syntax.Statement :=
  .select columns (some (pragmaOf function argument)) [] filter [] [] none none

/-- The result column of a name. -/
def named (text : String) : ResultColumn := .expression (name text) none text

/-- {lit}`CREATE TABLE s(schema)`. -/
def createS : Syntax.Statement := .createTable (name! "s") [typed "schema" none] []

/-- The kind of the restriction of the statement after {lit}`w` and {lit}`s` are created, or none
when it resolves. -/
def restrictionOf (statement : Syntax.Statement) : Option RestrictionKind :=
  match migration (catalogOf (migration [] [createW, createS])) [statement] with
  | .restricted restriction => some restriction.kind
  | .resolved .. => none

-- A name of arg or schema, in a condition, a result column, GROUP BY or USING, is the
-- restriction table-function, because SQLite gives a condition on it to the pragma.
example : restrictionOf (selectFrom [named "name"] "pragma_table_info" "w"
    (some (.compare .eq (name "schema") (.string "main".toUTF8.toList)))) = some .tableFunction := by decide +kernel
example : restrictionOf (selectFrom [named "arg"] "pragma_table_info" "w") = some .tableFunction := by decide +kernel
example : restrictionOf (.select [.expression (.callStar "count") none "count(*)"]
    (some (pragmaOf "pragma_table_info" "w")) [] none [name "schema"] [] none none) = some .tableFunction := by
  decide +kernel
example : restrictionOf (.select [.star] (some (pragmaOf "pragma_table_info" "s")) [usingSchema] none [] [] none
    none) = some .tableFunction := by decide +kernel
example : restrictionOf (selectFrom [named "name"] "pragma_table_info" "w") = none := by decide +kernel

end Belay.Sqlite.Model.PragmaSchemaExamples
