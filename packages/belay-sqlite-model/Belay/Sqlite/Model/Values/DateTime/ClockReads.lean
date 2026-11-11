import Belay.Sqlite.Model.Shared.Catalog.ExprAny
import Belay.Sqlite.Model.Values.DateTime.Functions

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- Whether a time value reads the clock in {lit}`parseDateOrTime`: text or a BLOB whose
bytes before the first NUL ({name}`bytesBeforeNul`) are {lit}`now`, {lit}`subsec` or
{lit}`subsecond` without ASCII case ({name}`equalsKeyword`). A BLOB counts because SQLite
reads it as its bytes ({lit}`sqlite3_value_text`). Every other value gives the same date
and time at every clock value. -/
def namesClock : Value → Bool
  | .text bytes | .blob bytes =>
    let text := bytesBeforeNul bytes
    equalsKeyword text nowKeyword || equalsKeyword text subsecKeyword || equalsKeyword text subsecondKeyword
  | .null | .integer _ | .real _ => false

end Belay.Sqlite.Model.Resolved
