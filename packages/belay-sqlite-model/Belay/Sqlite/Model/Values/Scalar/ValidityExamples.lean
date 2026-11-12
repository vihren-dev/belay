import Belay.Sqlite.Model.Shared.Execution.SqlExecution

set_option doc.verso true

namespace Belay.Sqlite.Model.ValidityExamples

open Belay.Sqlite.Model

/-- A text value. -/
def textValue (value : String) : Value := .text value.toUTF8.toList

end Belay.Sqlite.Model.ValidityExamples
