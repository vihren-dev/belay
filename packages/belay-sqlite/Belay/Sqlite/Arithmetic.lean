import Belay.Sqlite.NumberConvert
import Belay.Sqlite.RealText

set_option doc.verso true

/-! The arithmetic and the {lit}`CAST` of SQLite values (ADR 0012, slice 2), ported from
the pinned 3.51.0 source: the opcodes {lit}`OP_Add` to {lit}`OP_Remainder`, the numeric
type of a TEXT or BLOB operand ({lit}`computeNumericType`), and {lit}`sqlite3VdbeMemCast`.
Integer arithmetic stays exact while both operands are integers and the result fits in
64 bits; otherwise SQLite computes with doubles. -/

namespace Belay.Sqlite

/-- The least 64-bit signed integer. -/
def int64Minimum : Int := -(2 ^ 63)

/-- The greatest 64-bit signed integer. -/
def int64Maximum : Int := 2 ^ 63 - 1

/-- Whether an integer fits in 64 bits. -/
def fitsInt64Range (value : Int) : Bool := int64Minimum ≤ value && value ≤ int64Maximum

/-- A REAL value from a double; a NaN becomes NULL, as SQLite never stores a NaN. -/
def realValue (value : Float) : Value := if value.isNaN then .null else .real value.toBits

/-- The double of a value as {lit}`sqlite3VdbeRealValue` reads it: an integer converted,
a REAL as it is, TEXT and BLOB by {name}`atof`, NULL as zero. -/
def Value.toReal : Value → Float
  | .integer value => Float.ofInt value
  | .real bits => Float.ofBits bits
  | .text bytes | .blob bytes => (atof bytes).1
  | .null => 0

/-- The integer of a value as {lit}`sqlite3VdbeIntValue` reads it: a REAL by
{name}`realToI64`, TEXT and BLOB by {name}`atoi64`, NULL as zero. -/
def Value.toInt64 : Value → Int
  | .integer value => value
  | .real bits => realToI64 (Float.ofBits bits)
  | .text bytes | .blob bytes => (atoi64 bytes).1
  | .null => 0

/-- Whether a TEXT or BLOB operand counts as an integer in arithmetic
({lit}`computeNumericType`), with its integer when it does: the text is an integer form,
or a whole number with other text after it, that {name}`atoi64` reads. -/
def textInteger? (bytes : List UInt8) : Option Int :=
  let (_, code) := atof bytes
  let (integer, integerCode) := atoi64 bytes
  if code ≤ 0 then (if code == 0 && integerCode ≤ 1 then some integer else none)
  else if code == 1 && integerCode == 0 then some integer
  else none

/-- The integer of an operand for integer arithmetic, if it has one: an integer, or a
TEXT or BLOB that counts as one. -/
def Value.arithmeticInteger? : Value → Option Int
  | .integer value => some value
  | .text bytes | .blob bytes => textInteger? bytes
  | .null | .real _ => none

/-- An arithmetic operator of SQL. -/
inductive ArithmeticOperator where
  /-- {lit}`+`. -/
  | add
  /-- {lit}`-`. -/
  | subtract
  /-- {lit}`*`. -/
  | multiply
  /-- {lit}`/`. -/
  | divide
  /-- {lit}`%`. -/
  | remainder
  deriving Repr, DecidableEq

/-- The double result of an operator, as {lit}`fp_math` computes it, or NULL. A division
by zero gives NULL; the remainder converts both operands to integers, with a divisor of
{lit}`-1` read as 1. -/
def ArithmeticOperator.real (operator : ArithmeticOperator) (left right : Value) : Value :=
  let (a, b) := (left.toReal, right.toReal)
  match operator with
  | .add => realValue (a + b)
  | .subtract => realValue (a - b)
  | .multiply => realValue (a * b)
  | .divide => if b == 0 then .null else realValue (a / b)
  | .remainder =>
    let divisor := right.toInt64
    if divisor == 0 then .null
    else realValue (Float.ofInt (left.toInt64.tmod (if divisor == -1 then 1 else divisor)))

/-- The integer result of an operator on two 64-bit integers ({lit}`int_math`), or the
double result when it overflows. Division truncates toward zero; a zero divisor gives
NULL; {lit}`int64Minimum / -1` overflows; a remainder by {lit}`-1` is computed by 1. -/
def ArithmeticOperator.integer (operator : ArithmeticOperator) (left right : Value) (a b : Int) : Value :=
  let exact := fun (result : Int) => if fitsInt64Range result then Value.integer result else operator.real left right
  match operator with
  | .add => exact (a + b)
  | .subtract => exact (a - b)
  | .multiply => exact (a * b)
  | .divide => if b == 0 then .null else exact (a.tdiv b)
  | .remainder => if b == 0 then .null else .integer (a.tmod (if b == -1 then 1 else b))

/-- Whether a value is the NULL cell. -/
def Value.isNullCell : Value → Bool
  | .null => true
  | .integer _ | .real _ | .text _ | .blob _ => false

/-- SQLite's value of {lit}`left operator right`: NULL when an operand is NULL, integer
arithmetic when both operands are integers or count as integers, else double
arithmetic; a NaN result is NULL. -/
def ArithmeticOperator.apply (operator : ArithmeticOperator) (left right : Value) : Value :=
  if left.isNullCell || right.isNullCell then .null
  else match left.arithmeticInteger?, right.arithmeticInteger? with
    | some a, some b => operator.integer left right a b
    | some _, none | none, some _ | none, none => operator.real left right

/-- The bytes of a value converted to TEXT: an integer in decimal, a REAL by
{name}`realText`, TEXT and BLOB bytes as they are, NULL as no bytes. -/
def Value.textBytes : Value → List UInt8
  | .integer value => (toString value).toUTF8.toList
  | .real bits => (realText (Float.ofBits bits)).toUTF8.toList
  | .text bytes | .blob bytes => bytes
  | .null => []

/-- The magnitude bound of {lit}`sqlite3RealSameAsInt`: {lit}`2^51`. For a nonzero double,
only an integer in the half-open interval {lit}`[-2^51, 2^51)` can count as the same as
the double; a zero double counts as the same as every integer. -/
def realSameAsIntBound : Int := 2 ^ 51

/-- Whether a double equals a 64-bit integer for {lit}`sqlite3RealSameAsInt`: it is zero,
or the integer converts to the same double and lies in
{lit}`[-realSameAsIntBound, realSameAsIntBound)`. -/
def realSameAsInt (value : Float) (integer : Int) : Bool :=
  value == 0 || ((Float.ofInt integer).toBits == value.toBits && -realSameAsIntBound ≤ integer && integer < realSameAsIntBound)

/-- The value with NUMERIC affinity forced ({lit}`sqlite3VdbeMemNumerify`): a number stays;
a TEXT or BLOB becomes an integer when its integer form reads whole, or when its double
equals an integer, else a REAL. -/
def Value.numerify : Value → Value
  | .text bytes | .blob bytes =>
    let (double, code) := atof bytes
    let (whole, wholeCode) := atoi64 bytes
    if (code == 0 || code == 1) && wholeCode ≤ 1 then .integer whole
    else if realSameAsInt double (realToI64 double) then .integer (realToI64 double)
    else realValue double
  | value@(.null) | value@(.integer _) | value@(.real _) => value

/-- SQLite's {lit}`CAST(value AS type)` for the affinity of the type
({lit}`sqlite3VdbeMemCast`): NULL stays NULL; BLOB takes {name}`Value.textBytes`, which
keeps the bytes of a BLOB; NUMERIC is {name}`Value.numerify`; INTEGER and REAL read the
value as {name}`Value.toInt64` and {name}`Value.toReal` do; TEXT takes
{name}`Value.textBytes`. -/
def castValue (affinity : Affinity) (value : Value) : Value :=
  match value with
  | .null => .null
  | .integer _ | .real _ | .text _ | .blob _ => match affinity with
    | .blob => .blob value.textBytes
    | .numeric => value.numerify
    | .integer => .integer value.toInt64
    | .real => realValue value.toReal
    | .text => .text value.textBytes

end Belay.Sqlite
