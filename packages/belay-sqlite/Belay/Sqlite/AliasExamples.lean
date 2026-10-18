import Belay.Sqlite.SqlExecution

set_option doc.verso true

/-! Examples of rowid aliases (ADR 0012, amendment 4; slice 5b), checked by
{lit}`#guard`: the rowid and alias cell of inserted rows, {lit}`datatype mismatch`, its
order with constraint failures, and UPDATE of the alias. -/

namespace Belay.Sqlite.AliasExamples
open Belay.Sqlite

/-- {lit}`t(id INTEGER PRIMARY KEY, v)`: the alias at position 0, which is also the
primary key. -/
def shape : CatalogTable :=
  { columns := [{ name := "id", declaredType := some "INTEGER" }, { name := "v", declaredType := none }],
    primaryKey := [0], rowidAlias := some 0 }

/-- The table with the row {lit}`(5, 'a')` at rowid 5. -/
def table : Table := { shape, rows := [{ rowid := 5, values := [.integer 5, .text [97]] }] }

/-- A database with the table at position 0. -/
def database : Database := .ofTables [("t", table)]

/-- The rows of the table after a write, or none for a failure. -/
def rowsAfter : Outcome → Option (List Row)
  | .success database => (database.table 0).map (·.rows)
  | .failure .. | .pending .. => none

/-- The error of a failed write, or none. -/
def errorOf : Outcome → Option ExecutionError
  | .failure _ reason _ => some reason
  | .success _ | .pending .. => none

/-- INSERT of the rows into the table. -/
def insert (rows : List (List Value)) : Outcome := literalStep 0 (.insert 0 (rows.map (·.map .value)) []) database 0

/-- UPDATE of the alias to the value. -/
def update (value : Value) : Outcome := literalStep 0 (.update 0 [(0, .literal value)] none []) database 0

-- A NULL alias takes the next rowid, also into its cell; an integer alias is the rowid.
#guard rowsAfter (insert [[.null, .text [98]], [.integer (-3), .text [99]]]) ==
  some [{ rowid := 5, values := [.integer 5, .text [97]] }, { rowid := 6, values := [.integer 6, .text [98]] },
        { rowid := -3, values := [.integer (-3), .text [99]] }]
-- A text or real alias is SQLite's datatype mismatch; a duplicate alias is a unique failure.
#guard errorOf (insert [[.text [120], .null]]) == some .datatypeMismatch
#guard errorOf (insert [[.real 0x3FF8000000000000, .null]]) == some .datatypeMismatch
#guard errorOf (insert [[.integer 5, .null]]) == some .constraintViolation
-- Rows are inserted in order: the first failing row decides the error.
#guard errorOf (insert [[.integer 5, .null], [.text [120], .null]]) == some .constraintViolation
#guard errorOf (insert [[.text [120], .null], [.integer 5, .null]]) == some .datatypeMismatch
-- UPDATE of the alias moves the row; NULL and text are mismatches.
#guard rowsAfter (update (.integer 9)) == some [{ rowid := 9, values := [.integer 9, .text [97]] }]
#guard errorOf (update .null) == some .datatypeMismatch
#guard errorOf (update (.text [122])) == some .datatypeMismatch

end Belay.Sqlite.AliasExamples
