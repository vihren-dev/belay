import Belay.Sqlite.Model.Resolution.Examples
import Belay.Sqlite.Model.QueryFunctions

set_option doc.verso true

/-! Examples of joins (ADR 0012, amendment 2, slice 4), checked by {lit}`#guard`: the
resolution of sources and names, SQLite's prepare errors, the restrictions, and the rows
of inner and left joins. -/

namespace Belay.Sqlite.Model.Resolution.JoinExamples
open Belay.Sqlite.Model Syntax Resolution.Examples

/-- A catalog with {lit}`t(a INTEGER, b TEXT)` at position 0 and {lit}`u(a INTEGER, c TEXT)`
at position 1. -/
def tables : Catalog := catalogOf (schema [.createTable (name! "t") [column (name! "a") (some "INTEGER"), column (name! "b")] [],
  .createTable (name! "u") [column (name! "a") (some "INTEGER"), column (name! "c")] []])

/-- A table reference without an alias. -/
def table (name : Identifier) : TableReference := { table := name, alias := none }

/-- A join with the operator keywords to a table, with an optional ON condition. -/
def joined (operator : List String) (source : TableReference) (condition : Option Expr := none) : Join :=
  { operator, source, condition, usingColumns := none }

/-- {lit}`x.c` as written. -/
def qualified (source column : Identifier) : Expr := .qualified source column

/-- {lit}`t.a = u.a`. -/
def onA : Expr := .compare .eq (qualified (name! "t") (name! "a")) (qualified (name! "u") (name! "a"))

/-- The single statement of a resolution of a {lit}`SELECT *` with these sources. -/
def resolvedOne (results : List ResultColumn) (source : TableReference) (joins : List Join)
    (filter : Option Expr := none) : Option Resolved.Statement :=
  (statements (migration tables [.select results (some source) joins filter [] [] none none])).head?

/-- Whether the resolution is a model restriction. -/
def restrictedOne (results : List ResultColumn) (source : TableReference) (joins : List Join) : Bool :=
  restricted (migration tables [.select results (some source) joins none [] [] none none])

/-- The resolved join of {lit}`u` on {lit}`t.a = u.a`: the cell of {lit}`u.a` follows the two
cells of {lit}`t`. -/
def joinU : Resolved.QuerySource :=
  { kind := .inner, source := .table 1, condition := some (.compare .eq (some .numeric) (.column 0) (.column 2)) }

-- An inner join: `*` names the columns of both tables, and ON reads the joined row.
#guard resolvedOne [.star] (table (name! "t")) [joined [] (table (name! "u")) (some onA)] ==
  some (.query { sources := [.first 0, joinU], filter := none, aggregate := false, groupBy := [],
                 columns := [.scalar (.column 0), .scalar (.column 1), .scalar (.column 2), .scalar (.column 3)],
                 names := ["a", "b", "a", "c"], orderBy := [], offset := 0, limit := none } [])
-- An unqualified name of a column of both tables is SQLite's ambiguous column name.
#guard resolvedOne [.expression (.identifier (name! "a") .none) none "a"] (table (name! "t")) [joined [] (table (name! "u"))] ==
  some (.prepareError (.expression (.ambiguousColumn (name! "a"))))
-- An alias hides the table name; an unknown qualifier names no column; `x.*` of no source.
#guard resolvedOne [.expression (qualified (name! "t") (name! "a")) none "t.a"] { table := (name! "t"), alias := some (name! "x") } [] ==
  some (.prepareError (.expression (.noSuchColumn (name! "t.a"))))
#guard resolvedOne [.sourceStar (name! "zz")] (table (name! "t")) [] == some (.prepareError (.expression (.noSuchSource (name! "zz"))))
-- `x.*` in RETURNING is SQLite's prepare error, after the errors of the write itself.
#guard (statements (migration tables [(.delete (name! "t") none [.star, .sourceStar (name! "t")])])).head? ==
  some (.prepareError (.expression .returningSourceStar))
-- SQLite expands the wildcards first: `t.*` wins over a missing name in an earlier column.
#guard (statements (migration tables
  [(.delete (name! "t") none [.expression (.identifier (name! "zz") .none) none "zz", .sourceStar (name! "t")])])).head? ==
  some (.prepareError (.expression .returningSourceStar))
#guard (statements (migration tables
  [(.delete (name! "t") (some (.identifier (name! "zz") .none)) [.sourceStar (name! "t")])])).head? ==
  some (.prepareError (.expression (.noSuchColumn (name! "zz"))))
-- 65 tables are SQLite's limit error.
#guard resolvedOne [.star] (table (name! "t")) ((List.range 64).map fun item =>
  joined [] { table := (name! "t"), alias := some (Identifier.ofString s!"t{item}") }) == some (.prepareError (.expression .tooManyTables))
-- An operator that SQLite refuses (`unknown join type`) is a restriction.
#guard restrictedOne [.star] (table (name! "t")) [joined ["LEFT", "INNER"] (table (name! "u")) (some onA)]
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
