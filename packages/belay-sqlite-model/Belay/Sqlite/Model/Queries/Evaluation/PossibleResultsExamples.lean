import Belay.Sqlite.Model.Queries.Evaluation.PossibleResults
import Belay.Sqlite.Model.Shared.Execution.SqlExecution
import Belay.Sqlite.Model.Queries.Fixtures.Examples

set_option doc.verso true

namespace Belay.Sqlite.Model.PossibleResultsExamples

open Belay.Sqlite.Model Syntax

/-- A column with the type, or none. -/
def plain (text : String) (declaredType : Option String := none) : ColumnDefinition :=
  { name := Identifier.ofString text, declaredType, constraints := [] }

/-- A name as written. -/
def name (text : String) : Expr := .identifier (Identifier.ofString text) .none

/-- A text literal. -/
def text (value : String) : Expr := .string value.toUTF8.toList

/-- A text value. -/
def textValue (value : String) : Value := .text value.toUTF8.toList

/-- {lit}`SELECT columns FROM t [ORDER BY terms] [LIMIT limit] [OFFSET offset]`, with
{lit}`DISTINCT` and {lit}`GROUP BY` terms when given. -/
def selectT (columns : List Expr) (orderBy : List OrderTerm := []) (limit offset : Option Nat := none)
    (groupBy : List Expr := []) (distinct : Bool := false) : Syntax.Statement :=
  .select (columns.map fun column => .expression column none "") (some { table := Identifier.ofString "t", alias := none })
    [] none groupBy orderBy (limit.map fun n => .numeric (toString n)) (offset.map fun n => .numeric (toString n)) []
    none distinct

/-- An ascending {lit}`ORDER BY` term of a column. -/
def ascending (column : String) : OrderTerm := { expression := name column, descending := false }

/-- {lit}`CREATE TABLE t(id INTEGER PRIMARY KEY, name TEXT, p INTEGER)` with rows. -/
def withRows (rows : List (List Expr)) : List Syntax.Statement :=
  [.createTable (name! "t") [plain "id" (some "INTEGER"), plain "name" (some "TEXT"), plain "p" (some "INTEGER")] [],
   .insert (name! "t") none rows []]

/-- The guide's customers: bob before ada in rowid order. -/
def customers : List Syntax.Statement :=
  withRows [[.numeric "1", text "bob", .numeric "1"], [.numeric "2", text "ada", .numeric "1"]]

/-- Three rows of priority 1 and one of priority 2. -/
def jobs : List Syntax.Statement :=
  withRows [[.numeric "1", text "a", .numeric "1"], [.numeric "2", text "b", .numeric "1"],
    [.numeric "3", text "c", .numeric "1"], [.numeric "4", text "d", .numeric "2"]]

-- The normal form is one list for any input order: NULL comes before a NaN REAL, which
-- Value.compare alone would call equal, and the integer 1 before the real 1.0.
example : Resolved.normalForm [[.real 0x7FF8000000000000], [.null]] = Resolved.normalForm [[.null], [.real 0x7FF8000000000000]] := by
  decide +kernel
example : Resolved.normalForm [[.real 0x3FF0000000000000], [.integer 1]] = [[.integer 1], [.real 0x3FF0000000000000]] := by
  decide +kernel

end Belay.Sqlite.Model.PossibleResultsExamples
