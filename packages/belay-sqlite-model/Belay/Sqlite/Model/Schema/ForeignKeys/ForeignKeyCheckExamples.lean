import Belay.Sqlite.Model.Schema.Rows.ValidityExamples
import Belay.Sqlite.Model.Shared.Execution.ScriptRun

set_option doc.verso true

namespace Belay.Sqlite.Model.ForeignKeyCheckExamples

open Belay.Sqlite.Model Syntax Resolution.Examples ValidityExamples

/-- A column without a type that references the table {lit}`parent`, at the columns. -/
def refers (column parent : String) (columns : List String := []) : ColumnDefinition :=
  typed column none [.references (.ofString parent) (columns.map .ofString) .noAction .noAction]

/-- {lit}`CREATE TABLE p(x, y UNIQUE)`, {lit}`CREATE TABLE c2(a REFERENCES q)` and
{lit}`CREATE TABLE w(k PRIMARY KEY, a REFERENCES q, b REFERENCES p(y)) WITHOUT ROWID`, with the row
1 of {lit}`c2` and the rows {lit}`(1, 2, 3)` and {lit}`(0, NULL, 4)` of {lit}`w`. No table
{lit}`q` exists. -/
def orphans : List Syntax.Statement :=
  [.createTable (name! "p") [typed "x" none, typed "y" none [.unique]] [],
   .createTable (name! "c2") [refers "a" "q"] [], .insert (name! "c2") none [[.numeric "1"]] [],
   .createTable (name! "w") [typed "k" none [.primaryKey false], refers "a" "q", refers "b" "p" ["y"]] []
     { withoutRowid := true },
   .insert (name! "w") none [[.numeric "1", .numeric "2", .numeric "3"], [.numeric "0", .null, .numeric "4"]] []]

/-- The rows of the pragma with the table name, the rowid, the parent and the id. -/
def keyRow (table : String) (rowid : Option Int) (parent : String) (id : Int) : List Value :=
  [textValue table, (rowid.map Value.integer).getD .null, textValue parent, .integer id]

-- For each row in scan order, for each key by id: the key of the last column has id 0. A NULL
-- satisfies its key, and a missing parent table finds no row. A WITHOUT ROWID table has no rowid.
example : (built orphans).foreignKeyCheckRows (some 2) =
    some [keyRow "w" none "p" 0, keyRow "w" none "p" 0, keyRow "w" none "q" 1] := by decide +kernel

-- The rows are no rows exactly when the foreign keys hold.
example : (built orphans).foreignKeyCheckRows none = none ∧ ¬(built orphans).RowReferencesHold (built orphans).catalog.foreignKeyMapping := by decide +kernel
example : (built (orphans.take 2)).foreignKeyCheckRows none = some [] ∧ (built (orphans.take 2)).RowReferencesHold (built (orphans.take 2)).catalog.foreignKeyMapping := by
  decide +kernel

/-- {lit}`CREATE TABLE c1(a REFERENCES p(x))`, whose parent column has no unique index. -/
def mismatched (table : String) : Syntax.Statement := .createTable (.ofString table) [refers "a" "p" ["x"]] []

-- A mismatch fails at prepare, before any row, also when another table gives rows. Two tables
-- with a mismatch are a restriction, because SQLite reports the first in its own order.
example : (statements (migration [] (orphans ++ [mismatched "c1", .pragma (.foreignKeyCheck none)]))).getLast? =
    some (.prepareError (.foreignKeyMismatch (name! "c1") (name! "p"))) := by decide +kernel
example : (statements (migration [] (orphans ++ [mismatched "c1", .pragma (.foreignKeyCheck (some (name! "c2")))]))).getLast?.map
    (·.isControl) = some false := by decide +kernel
example : restricted (migration [] (orphans ++ [mismatched "c1", mismatched "c3", .pragma (.foreignKeyCheck none)])) = true := by
  decide +kernel

end Belay.Sqlite.Model.ForeignKeyCheckExamples
