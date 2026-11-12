import Belay.Sqlite.Model.Queries.Fixtures.Examples
import Belay.Sqlite.Model.Queries.Evaluation.QueryFunctions
import Belay.Sqlite.Model.Queries.Select.Sources

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.JoinExamples
open Belay.Sqlite.Model Syntax

/-- A table reference without an alias. -/
def table (name : Identifier) : TableReference := { table := name, alias := none }

/-- A join with the operator keywords to a table, with an optional ON condition. -/
def joined (operator : List String) (source : TableReference) (condition : Option Expr := none) : Join :=
  { operator, source, condition, usingColumns := none }

/-- {lit}`x.c` as written. -/
def qualified (source column : Identifier) : Expr := .qualified source column

/-- {lit}`t.a = u.a`. -/
def onA : Expr := .compare .eq (qualified (name! "t") (name! "a")) (qualified (name! "u") (name! "a"))

/-- The resolved join of {lit}`u` on {lit}`t.a = u.a`: the cell of {lit}`u.a` follows the two
cells of {lit}`t`. -/
def joinU : Resolved.QuerySource :=
  { kind := .inner, source := .table 1, condition := some (.compare .eq (some .numeric) (.column 0) (.column 2)) }

-- Lean reads the operator keywords as SQLite's sqlite3JoinType does: without ASCII case, in
-- any order and repeated (checked natively).
#guard joinOperator ["Left", "outer"] == some (.left, false)
#guard joinOperator ["OUTER", "LEFT"] == some (.left, false) && joinOperator ["left", "left"] == some (.left, false)
#guard joinOperator ["NATURAL", "cross"] == some (.inner, true) && joinOperator ["outer", "natural", "full"] == some (.full, true)
#guard joinOperator ["left", "inner"] == none && joinOperator ["outer"] == none && joinOperator ["sideways"] == none

/-- A table of two rows, with {lit}`a` 1 and 2. -/
def left : Table :=
  { shape := { columns := [{ name := (name! "a"), declaredType := some "INTEGER" }] },
    rows := [{ rowid := 1, values := [.integer 1] }, { rowid := 2, values := [.integer 2] }] }

/-- A table of one row, with {lit}`a` 1. -/
def right : Table :=
  { shape := { columns := [{ name := (name! "a"), declaredType := some "INTEGER" }] },
    rows := [{ rowid := 1, values := [.integer 1] }] }

/-- The join condition {lit}`left.a = right.a` over the joined row. -/
def equal : Option Resolved.Expr := some (.compare .eq none (.column 0) (.column 1))

-- An inner join keeps the matching row; a left join also pads the unmatched left row.
#guard Resolved.joinRows (.plain 0) 1 (Resolved.sourceRows left) { kind := .inner, source := .table 1, condition := equal } 1
    (Resolved.sourceRows right) ==
  [[.integer 1, .integer 1]]
#guard Resolved.joinRows (.plain 0) 1 (Resolved.sourceRows left) { kind := .left, source := .table 1, condition := equal } 1
    (Resolved.sourceRows right) ==
  [[.integer 1, .integer 1], [.integer 2, .null]]

end Belay.Sqlite.Model.Resolution.JoinExamples
