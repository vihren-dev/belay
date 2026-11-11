import Belay.Sqlite.Model.Shared.Values.NumberConvert
import Belay.Sqlite.Model.Values.Scalar.NumberConvert
import Belay.Sqlite.Model.Frontend.Grammar.Operators
import Belay.Sqlite.Model.Values.Scalar.RealText

set_option doc.verso true

/-! The arithmetic and the {lit}`CAST` of SQLite values (ADR 0012, slice 2), ported from
the pinned 3.51.0 source: the opcodes {lit}`OP_Add` to {lit}`OP_Remainder`, the numeric
type of a TEXT or BLOB operand ({lit}`computeNumericType`), and {lit}`sqlite3VdbeMemCast`.
Integer arithmetic stays exact while both operands are integers and the result fits in
64 bits; otherwise SQLite computes with doubles. -/

namespace Belay.Sqlite.Model

/-- A value bound to a parameter, as a statement reads it: a NaN REAL is NULL, because
{lit}`sqlite3_bind_double` binds a NaN as NULL; every other value is the same. -/
def boundValue : Value → Value
  | .real bits => if (Float.ofBits bits).isNaN then .null else .real bits
  | .null => .null
  | .integer value => .integer value
  | .text bytes => .text bytes
  | .blob bytes => .blob bytes

/-- The value of parameter {lit}`number` of a statement, from the values bound to its parameters
in order, as the statement reads it ({name}`boundValue`): NULL when no value is bound to it, as
for a statement that binds no values. Parameter numbers start at 1. -/
def parameterValue (parameters : List Value) (number : Nat) : Value :=
  boundValue (parameters.getD (number - 1) .null)

end Belay.Sqlite.Model
