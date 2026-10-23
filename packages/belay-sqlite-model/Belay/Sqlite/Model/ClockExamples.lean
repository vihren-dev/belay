import Belay.Sqlite.Model.SqlExecution
import Belay.Sqlite.Model.Resolution.Examples

set_option doc.verso true

/-! Checked examples of scripts that read the clock (ADR 0012, amendment 5, slice 6e2):
each statement sees the clock value of its position, a {lit}`DEFAULT CURRENT_TIMESTAMP`
column gets the value of the INSERT's clock, ADD COLUMN with that default fails on a
populated table, and a script without time keywords has one outcome at every clock
assignment. Each expected value was checked against native SQLite 3.51.0. -/

namespace Belay.Sqlite.Model.ClockExamples
open Belay.Sqlite.Model Syntax Resolution.Examples

/-- The text value with the UTF-8 bytes of a string, to write expected results. -/
def textOf (text : String) : Value := .text text.toUTF8.toList

/-- {lit}`2024-12-31 23:59:59.999` in Julian-day milliseconds. -/
def lastClockOf2024 : Int := 212602449599999

/-- {lit}`2025-01-01 00:00:00` in Julian-day milliseconds. -/
def firstClockOf2025 : Int := 212602449600000

/-- The clock assignment that gives the first statement {name}`lastClockOf2024` and every
later statement {name}`firstClockOf2025`. -/
def newYear : Clock := fun position => if position = 0 then lastClockOf2024 else firstClockOf2025

/-- A column with a declared type and a time keyword as its default, such as
{lit}`b INTEGER DEFAULT CURRENT_TIMESTAMP`. -/
def timeDefault (name : Identifier) (declaredType : Option String) (keyword : String) : ColumnDefinition :=
  { name, declaredType, constraints := [.default (.currentTime keyword) keyword] }

/-- {lit}`CREATE TABLE t(a TEXT, b INTEGER DEFAULT CURRENT_TIMESTAMP)`. -/
def createT : Syntax.Statement :=
  .createTable (name! "t") [column (name! "a"), timeDefault (name! "b") (some "INTEGER") "CURRENT_TIMESTAMP"] []

/-- The catalog that {name}`createT` describes. -/
def catalogT : Catalog := catalogOf (schema [createT])

/-- The empty table of {name}`createT` at position 0. -/
def emptyT : Database := catalogT.emptyDatabase

/-- The values of the rows of table 0 after a script, or none when it fails. -/
def rowsAfter (clock : Clock) (script : List Syntax.Statement) : Option (List (List Value)) :=
  match runSqlAt clock (bindValues (statements (migration catalogT script)) []) emptyT with
  | .success database => (database.table 0).map (·.rows.map (·.values))
  | .failure .. | .pending .. => none

-- Two INSERTs see the clock values of their positions; the omitted column b gets the
-- timestamp of its own statement, and its INTEGER affinity keeps the text.
#guard rowsAfter newYear [.insert (name! "t") (some [(name! "a")]) [[.currentTime "CURRENT_DATE"]] [],
    .insert (name! "t") (some [(name! "a")]) [[.currentTime "CURRENT_TIME"]] []] ==
  some [[textOf "2024-12-31", textOf "2024-12-31 23:59:59"], [textOf "00:00:00", textOf "2025-01-01 00:00:00"]]
-- Every statement at one clock value gives one date.
#guard rowsAfter (fun _ => firstClockOf2025) [.insert (name! "t") (some [(name! "a")]) [[.currentTime "CURRENT_DATE"]] [],
    .insert (name! "t") (some [(name! "a")]) [[.currentTime "CURRENT_DATE"]] []] ==
  some [[textOf "2025-01-01", textOf "2025-01-01 00:00:00"], [textOf "2025-01-01", textOf "2025-01-01 00:00:00"]]
-- A clock of zero gives NULL for the keyword and the default.
#guard rowsAfter (fun _ => 0) [.insert (name! "t") (some [(name! "a")]) [[.currentTime "CURRENT_TIMESTAMP"]] []] ==
  some [[.null, .null]]

-- A VALUES item that reads the clock is stored with its column's affinity: the text of
-- `strftime('%s', 'now')` stays TEXT in a and becomes an INTEGER in b (checked natively).
#guard rowsAfter newYear [.insert (name! "t") (some [(name! "a"), (name! "b")])
    [[.call "strftime" [.string "%s".toUTF8.toList, .string "now".toUTF8.toList],
      .call "strftime" [.string "%s".toUTF8.toList, .string "now".toUTF8.toList]]] []] ==
  some [[textOf "1735689599", .integer 1735689599]]
-- Each time keyword is its date and time function without arguments.
example (clock : Int) : TimeKeyword.timestamp.value clock = Resolved.DateFunction.datetime.value clock [] := rfl

-- SQLite reads a time value up to its first NUL: `date('now' || char(0) || 'x')` is the date
-- of the statement's clock, and `date('nowx')` is NULL.
#guard rowsAfter newYear [.insert (name! "t") (some [(name! "a"), (name! "b")])
    [[.call "date" [.string [110, 111, 119, 0, 120]], .call "date" [.string [110, 111, 119, 120]]]] []] ==
  some [[textOf "2024-12-31", .null]]

/-- The resolved script {lit}`INSERT INTO t(a, b) VALUES ('x', 1)`, which reads no clock. -/
def clockFree : List Resolved.Statement := [.insert 0 [[.value (.text [120]), .value (.integer 1)]] []]

-- It is the resolution of the statement.
#guard statements (migration catalogT [.insert (name! "t") (some [(name! "a"), (name! "b")]) [[.string [120], .numeric "1"]] []]) == clockFree

/-- For every clock assignment and list of values, {name}`clockFree` with the values has the
outcome of {name}`runSql`. -/
example (clock : Clock) (values : List Value) :
    runSqlAt clock (bindValues clockFree [values]) emptyT = runSql (bindValues clockFree [values]) emptyT :=
  runSqlAt_of_readsClock clock _ emptyT (by rw [map_fst_bindValues]; decide)

-- ADD COLUMN with a time default fails on a populated table and succeeds on an empty one.
#guard (match runSqlAt (fun _ => firstClockOf2025) (bindValues (statements (migration catalogT
    [.insert (name! "t") (some [(name! "a")]) [[.null]] [],
     .addColumn (name! "t") (timeDefault (name! "c") none "CURRENT_DATE")])) []) emptyT with
  | .failure 1 .nonConstantColumnDefault _ => true
  | .success _ | .failure .. | .pending .. => false)
#guard (match runSqlAt (fun _ => firstClockOf2025) (bindValues (statements (migration catalogT
    [.addColumn (name! "t") (timeDefault (name! "c") none "CURRENT_DATE")])) []) emptyT with
  | .success _ => true
  | .failure .. | .pending .. => false)

end Belay.Sqlite.Model.ClockExamples
