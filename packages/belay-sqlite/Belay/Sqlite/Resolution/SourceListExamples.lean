import Belay.Sqlite.Resolution.JoinExamples
import Belay.Sqlite.QueryRun

set_option doc.verso true

/-! Examples of the source list in written order (ADR 0013, D5), checked by {lit}`#guard`:
{lit}`json_each` before a table, {lit}`LEFT JOIN json_each` with a correlated argument, and
the forms that stay restricted. Each row list was checked on native SQLite 3.51.0 with
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

/-- The result rows of a {lit}`SELECT` with these result columns and sources over
{name}`database`; none when it does not resolve to a query or a table is missing. -/
def rowsOf (results : List ResultColumn) (source : TableReference) (joins : List Join) : Option (List (List Value)) :=
  match resolvedOne results source joins with
  | some (.query query) => (query.source database).map fun source => query.results source.rows
  | _ => none

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
-- An argument that reads a later source is restricted, also when the later source is a table.
#guard restrictedOne [.star] (each "e" (qualified "t" "b")) [joined [] (table "t")]

end Belay.Sqlite.Resolution.SourceListExamples
