import Belay.Sqlite.Model.Arithmetic
import Belay.Sqlite.Model.ByteText

set_option doc.verso true

/-! What the scalar functions of ADR 0015 share: why a function gives no value, and the text
of an argument as a C function reads it. -/

namespace Belay.Sqlite.Model.Resolved

/-- Why a scalar function gives no value. -/
inductive FunctionFailure where
  /-- SQLite fails the statement while it runs, for example {lit}`integer overflow` of
  {lit}`abs`. -/
  | error
  /-- The model does not describe the value, for example a {lit}`zeroblob` larger than
  {lit}`zeroblobLimit`. -/
  | unmodeled
  deriving Repr, DecidableEq

/-- The text of a value as a function sees it ({lit}`sqlite3_value_text`): none for NULL, else
the bytes of {lit}`Value.textBytes` before the first NUL, as a C string. -/
def cText? : Value → Option (List UInt8)
  | .null => none
  | value@(.integer _) | value@(.real _) | value@(.text _) | value@(.blob _) => some (bytesBeforeNul value.textBytes)

end Belay.Sqlite.Model.Resolved
