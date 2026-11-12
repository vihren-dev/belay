import Belay.Sqlite.Model.Shared.Execution.SqlAdvance

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- A clock assignment: the clock value that the statement at each zero-based position
sees, in SQLite's Julian-day milliseconds (what the VFS method {lit}`xCurrentTimeInt64`
returns). Use {lean}`(fun _ => 0 : Clock)` when no statement reads the clock. -/
abbrev Clock := Nat → Int

end Belay.Sqlite.Model
