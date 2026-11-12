import Belay.Sqlite.Model.Shared.Values.Arithmetic
import Belay.Sqlite.Model.Shared.Values.Declarations

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The bits of the double {lit}`-0.0`. -/
def negativeZeroBits : UInt64 := 0x8000000000000000

/-- A REAL's bits with {lit}`-0.0` replaced by {lit}`+0.0`; every other value keeps its bits. -/
def positiveZero (bits : UInt64) : UInt64 := if bits == negativeZeroBits then 0 else bits

/-- The 64-bit integer of a REAL for {lit}`sqlite3VdbeIntegerAffinity`: the integer when the
double converts to a 64-bit integer and back without change and the integer is neither
the least nor the greatest 64-bit integer; otherwise none. -/
def wholeReal (bits : UInt64) : Option Int :=
  let whole := realToI64 (Float.ofBits bits)
  if Float.ofBits bits == Float.ofInt whole && int64Minimum < whole && whole < int64Maximum then some whole
  else none

/-- SQLite's {lit}`sqlite3VdbeIntegerAffinity` on a REAL: the integer of {name}`wholeReal`
when there is one, otherwise the REAL with the same bits, which are not NaN because they
are a REAL's.
{assert}`integerAffinity (5.0 : Float).toBits = .integer 5`. -/
def integerAffinity (bits : UInt64) : Value :=
  match wholeReal bits with
  | some whole => .integer whole
  | none => .real bits

/-- The read of a stored value from a REAL column ({lit}`OP_RealAffinity`): an integer
becomes its double, and every REAL result goes through {name}`positiveZero`; NULL, TEXT
and BLOB stay. No result is NaN: the double of an integer is a number, and a REAL keeps
its bits up to the sign of zero. -/
def realRead : Value → Value
  | .integer whole => .real (positiveZero (Float.ofInt whole).toBits)
  | .real bits => .real (positiveZero bits)
  | value@(.null) | value@(.text _) | value@(.blob _) => value

end Belay.Sqlite.Model
