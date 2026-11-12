import Lean.Elab.Term
import Belay.Sqlite.Model

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term

/-- The time of the text in Julian-day milliseconds, as SQLite's date functions read a time
value without modifiers ({name}`Belay.Sqlite.Model.DateTime.ofArguments`): a date, a date and a
time, a time on 2000-01-01, or a Julian day number, each in UTC. It is
{lean}`(none : Option Int)` for a text that the functions do not read as a time, for a time
after 9999-12-31 23:59:59.999 or before the first Julian day ({name}`Belay.Sqlite.Model.validJulianDay`),
and for {lit}`now`, which reads the clock. -/
def timeOfText? (text : String) : Option Int :=
  (Belay.Sqlite.Model.DateTime.ofArguments 0 [.text text.toUTF8.toList]).map
    (·.computeJulianDay.julianMilliseconds)

end Belay.Sqlite
