import Belay.Sqlite.Model.Schema.Dispatch.Examples
import Belay.Sqlite.Model.Schema.Dispatch.QueryFunctions
import Belay.Sqlite.Model.Queries.Select.JoinExamples

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

/-- The single statement of a resolution of a {lit}`SELECT *` with these sources. -/
def resolvedOne (results : List ResultColumn) (source : TableReference) (joins : List Join)
    (filter : Option Expr := none) : Option Resolved.Statement :=
  (statements (migration tables [.select results (some source) joins filter [] [] none none])).head?

/-- Whether the resolution is a model restriction. -/
def restrictedOne (results : List ResultColumn) (source : TableReference) (joins : List Join) : Bool :=
  restricted (migration tables [.select results (some source) joins none [] [] none none])

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
-- SQLite resolves a result column alias in ON as it does in WHERE (checked natively), so the model
-- refuses it instead of reporting a missing column. A name that is a column of the sources is no alias.
#guard restrictedOne [.expression (qualified (name! "t") (name! "b")) (some (name! "z")) "t.b AS z"] (table (name! "t"))
  [joined [] (table (name! "u")) (some (.compare .eq (.identifier (name! "z") .none) (qualified (name! "u") (name! "c"))))]
#guard !restrictedOne [.expression (qualified (name! "t") (name! "b")) (some (name! "c")) "t.b AS c"] (table (name! "t"))
  [joined [] (table (name! "u")) (some (.compare .eq (qualified (name! "t") (name! "a")) (qualified (name! "u") (name! "a"))))]

end Belay.Sqlite.Model.Resolution.JoinExamples
