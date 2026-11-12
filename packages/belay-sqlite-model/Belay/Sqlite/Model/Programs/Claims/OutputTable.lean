import Belay.Sqlite.Model.Programs.Claims.OutputRepr
import Belay.Sqlite.Model.Programs.Scripts.ScriptRun

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The value as a cell of a table: a text as its characters, without quotes; NULL as
{lit}`NULL`; another value as {name}`Value.display` shows it. -/
def Value.cellText : Value → String
  | .null => "NULL"
  | .text bytes => match String.fromUTF8? ⟨bytes.toArray⟩ with
    | some decoded => decoded
    | none => s!"text x'{hexBytes bytes}'"
  | value@(.integer _) | value@(.real _) | value@(.blob _) => toString (Value.display value)

end Belay.Sqlite.Model
