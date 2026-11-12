import Belay.Sqlite.Model.Shared.Execution.SqlExecution

set_option doc.verso true

namespace Belay.Sqlite.Model.ClockExamples
open Belay.Sqlite.Model

/-- The text value with the UTF-8 bytes of a string, to write expected results. -/
def textOf (text : String) : Value := .text text.toUTF8.toList

end Belay.Sqlite.Model.ClockExamples
