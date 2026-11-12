import Belay.Sqlite.Model.Queries.Evaluation.Arithmetic
import Belay.Sqlite.Model.Values.DateTime.Functions

set_option doc.verso true

/-! The six date and time functions with their modifiers, ported from the pinned SQLite
3.51.0 {lit}`date.c` (ADR 0012, amendment 5, slices 6f and 6g): {lit}`isDate`, then
{lit}`juliandayFunc`, {lit}`unixepochFunc`, {lit}`datetimeFunc`, {lit}`timeFunc`,
{lit}`dateFunc` and {lit}`strftimeFunc`. The model calls these functions only where
SQLite's {lit}`sqlite3NotPureFunc` passes, so {lit}`now` always reads the clock. -/

namespace Belay.Sqlite.Model

/-- The date and time function that a time keyword calls without arguments, as SQLite's
{lit}`ctimeFunc`, {lit}`cdateFunc` and {lit}`ctimestampFunc` do: {lit}`time`, {lit}`date`
and {lit}`datetime`. -/
def TimeKeyword.dateFunction : TimeKeyword → Resolved.DateFunction
  | .time => .time
  | .date => .date
  | .timestamp => .datetime

/-- The value that SQLite gives for the keyword when the statement's clock, as the VFS
method {lit}`xCurrentTimeInt64` returns it (Julian-day milliseconds), is {lit}`clock`: the
value of its date and time function without arguments ({name}`TimeKeyword.dateFunction`).
It is NULL for a clock of zero or less, where {lit}`setDateTimeToCurrent` fails, and text
otherwise. -/
def TimeKeyword.value (keyword : TimeKeyword) (clock : Int) : Value :=
  keyword.dateFunction.value clock []

end Belay.Sqlite.Model
