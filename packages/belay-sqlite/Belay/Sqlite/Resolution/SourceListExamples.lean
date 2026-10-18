import Belay.Sqlite.Resolution.JoinExamples
import Belay.Sqlite.QueryRun

set_option doc.verso true

/-! Examples of the source list in written order (ADR 0013, D5), checked by {lit}`#guard`:
{lit}`json_each` before a table, {lit}`LEFT JOIN json_each` with a correlated argument, the
forms that stay restricted, and two sources with the same name. Each row list was checked on native SQLite 3.51.0 with
the same schema and rows. -/

namespace Belay.Sqlite.Resolution.SourceListExamples
open Belay.Sqlite Syntax Resolution.Examples Resolution.JoinExamples

/-- The text value of a string. -/
def text (value : String) : Value := .text value.toUTF8.toList

/-- The database over {name}`tables`: {lit}`t` has the rows {lit}`(1, '[1,2]')` and
{lit}`(2, '[]')`, and {lit}`u` has no row. -/
def database : Database :=
  { catalog := tables,
    rows := [[{ rowid := 1, values := [.integer 1, text "[1,2]"] }, { rowid := 2, values := [.integer 2, text "[]"] }],
      []] }

/-- {lit}`json_each(argument) AS alias`. -/
def each (alias : String) (argument : Expr) : TableReference :=
  { table := "json_each", alias := some alias, arguments := some [argument] }

/-- The query of a resolved statement; none for any other statement and for no statement. -/
def queryOf : Option Resolved.Statement → Option Resolved.Query
  | some (.query query) => some query
  | some (.createTable ..) | some (.createIndex ..) | some (.addColumn ..) | some .begin | some .commit
  | some .rollback | some (.insert ..) | some (.update ..) | some (.upsert ..) | some (.delete ..)
  | some (.prepareError _) | some (.clocked ..) | none => none

/-- The result rows of a {lit}`SELECT` with these result columns and sources over
{name}`database`; none when it does not resolve to a query or a table is missing. -/
def rowsOf (results : List ResultColumn) (source : TableReference) (joins : List Join) : Option (List (List Value)) :=
  (queryOf (resolvedOne results source joins)).bind fun query =>
    (query.source 0 database).map fun source => query.results 0 source.rows

/-- A result column of {lit}`x.c`. -/
def named (source column : String) : ResultColumn := .expression (qualified source column) none s!"{source}.{column}"

-- `SELECT e.value, t.a FROM json_each('[5,6]') AS e, t`: a table after json_each. Native SQLite
-- scans `t` first; without ORDER BY the order of the rows is not defined.
#guard rowsOf [named "e" "value", named "t" "a"] (each "e" (.string "[5,6]".toUTF8.toList)) [joined [] (table "t")] ==
  some [[.integer 5, .integer 1], [.integer 5, .integer 2], [.integer 6, .integer 1], [.integer 6, .integer 2]]
-- `SELECT t.a, e.value FROM t LEFT JOIN json_each(t.b) AS e`: the row without an element is padded.
#guard rowsOf [named "t" "a", named "e" "value"] (table "t") [joined ["LEFT"] (each "e" (qualified "t" "b"))] ==
  some [[.integer 1, .integer 1], [.integer 1, .integer 2], [.integer 2, .null]]
-- `SELECT t.a, e.value FROM t JOIN json_each(t.b) AS e`: an inner join keeps no row for `[]`.
#guard rowsOf [named "t" "a", named "e" "value"] (table "t") [joined [] (each "e" (qualified "t" "b"))] ==
  some [[.integer 1, .integer 1], [.integer 1, .integer 2]]
-- json_each as the right operand of RIGHT JOIN, and with NATURAL or USING, is restricted.
#guard restrictedOne [.star] (table "t") [joined ["RIGHT"] (each "e" (qualified "t" "b"))]
#guard restrictedOne [.star] (table "t") [joined ["NATURAL"] (each "e" (qualified "t" "b"))]
#guard restrictedOne [.star] (table "t") [{ joined [] (each "e" (qualified "t" "b")) with usingColumns := some ["a"] }]
-- NATURAL after json_each is restricted: SQLite skips the hidden columns `json` and `root`.
#guard restrictedOne [.star] (each "e" (qualified "t" "b")) [joined ["NATURAL"] (table "u")]
-- An argument that reads a later source is restricted, also when the later source is a table.
#guard restrictedOne [.star] (each "e" (qualified "t" "b")) [joined [] (table "t")]

/-- The resolution of {lit}`SELECT results FROM t, t`, two sources with the same name. -/
def overTwice (results : List ResultColumn) (joins : List Join := [joined [] (table "t")]) : Option Resolved.Statement :=
  resolvedOne results (table "t") joins

-- `SELECT count(*) FROM t, t` counts every pair of rows: 4.
#guard rowsOf [.expression (.callStar "count") none "count(*)"] (table "t") [joined [] (table "t")] ==
  some [[.integer 4]]
-- Over two sources named `t`, a name, a qualified name, `t.*` and `*` are ambiguous; the
-- expansion of a star names the schema, the source and the declared column.
#guard overTwice [.expression (.identifier "a" .none) none "a"] == some (.prepareError (.ambiguousColumn "a"))
#guard overTwice [.expression (qualified "t" "a") none "t.a"] == some (.prepareError (.ambiguousColumn "t.a"))
#guard overTwice [.sourceStar "t"] == some (.prepareError (.ambiguousColumn "main.t.a"))
#guard overTwice [.star] == some (.prepareError (.ambiguousColumn "main.t.a"))
-- A source is named by its alias, else by the table name as declared: `FROM T, t`.
#guard resolvedOne [.star] (table "T") [joined [] (table "t")] == some (.prepareError (.ambiguousColumn "main.t.a"))
-- `FROM t JOIN t USING (a)`: `t.a` is the left column, `t.b` and `*` are ambiguous.
#guard (queryOf (overTwice [.expression (qualified "t" "a") none "t.a"]
  [{ joined [] (table "t") with usingColumns := some ["a"] }])).map (·.columns) == some [.scalar (.column 0)]
#guard overTwice [.expression (qualified "t" "b") none "t.b"] [{ joined [] (table "t") with usingColumns := some ["a"] }] ==
  some (.prepareError (.ambiguousColumn "t.b"))
#guard overTwice [.star] [{ joined [] (table "t") with usingColumns := some ["a"] }] ==
  some (.prepareError (.ambiguousColumn "main.t.b"))
-- `SELECT t.c FROM t, u AS t`: only the second source named `t` has `c`.
#guard (queryOf (resolvedOne [.expression (qualified "t" "c") none "t.c"] (table "t")
  [joined [] { table := "u", alias := some "t" }])).map (·.columns) == some [.scalar (.column 3)]

end Belay.Sqlite.Resolution.SourceListExamples
