import Belay.Sqlite.Model.Values.Scalar.Scalar

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved.FunctionExamples

open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- The UTF-8 bytes of a string. -/
def text (value : String) : Value := .text value.toUTF8.toList

end Belay.Sqlite.Model.Resolved.FunctionExamples
