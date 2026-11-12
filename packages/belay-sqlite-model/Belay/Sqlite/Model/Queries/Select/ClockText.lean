import Belay.Sqlite.Model.Shared.Resolved.ClockText

set_option doc.verso true

/-! The time keywords and the parts of the pinned SQLite 3.51.0 {lit}`date.c` that the
date and time functions of {lit}`Date/` build on: the valid range of Julian days, the
civil date of a Julian day, 64-bit wrapping and the digit bytes. A keyword's value is its
date and time function without arguments ({lit}`TimeKeyword.value`).

{lit}`computeYMD` uses doubles. The integer formulas here give the same result for every
day number in the valid range; a check over all 5373486 day numbers confirmed it. -/

namespace Belay.Sqlite.Model

/-- The time keyword of a keyword as written, which SQLite compares without ASCII case:
{lit}`CURRENT_TIME`, {lit}`CURRENT_DATE`, or else {lit}`CURRENT_TIMESTAMP`, the only other
keyword that the frontend maps to {lit}`Syntax.Expr.currentTime`. -/
def timeKeywordNamed (keyword : String) : TimeKeyword :=
  match keyword.toLower with
  | "current_time" => .time
  | "current_date" => .date
  | _ => .timestamp

end Belay.Sqlite.Model
