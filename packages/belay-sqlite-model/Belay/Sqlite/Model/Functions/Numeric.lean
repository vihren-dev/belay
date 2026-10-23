import Belay.Sqlite.Model.Arithmetic
import Belay.Sqlite.Model.RealText
import Belay.Sqlite.Model.StoreValue

set_option doc.verso true

/-! The exact numeric functions of ADR 0015, slice 2, from SQLite 3.51.0's {lit}`func.c`:
{lit}`round`, {lit}`floor`, {lit}`ceil`, {lit}`trunc`, {lit}`sqrt`, {lit}`pi`, {lit}`degrees`,
{lit}`radians` and {lit}`mod`. Each is an exact IEEE operation or a rounding to an integer, so
its result does not depend on the C library; each is written with the operations that the
kernel reduces ({lit}`Float` addition, multiplication, division, {lit}`sqrt`, {lit}`toInt64`,
{lit}`ofInt`) and with integer arithmetic on the bits. -/

namespace Belay.Sqlite.Model.Resolved

/-- 2^52: every double of this magnitude or more is an integer. -/
def integralBound : Float := 4503599627370496.0

/-- Whether the sign bit of a double is set, also for {lit}`-0.0`. -/
def signBit (value : Float) : Bool := value.toBits >>> 63 == 1

/-- A zero result with the sign of {lit}`value`, as the C functions give it; another result as
it is. -/
def withZeroSign (value result : Float) : Float :=
  if result == 0 then (if signBit value then -(0.0 : Float) else 0.0) else result

/-- The double truncated toward zero ({lit}`trunc`): below {name}`integralBound` by the integer
conversion, else as it is (also an infinity or NaN). A zero keeps the sign of the value. -/
def truncDouble (value : Float) : Float :=
  if value.abs < integralBound then withZeroSign value (Float.ofInt value.toInt64.toInt) else value

/-- The greatest integral double not above the value ({lit}`floor`). -/
def floorDouble (value : Float) : Float :=
  if value.abs < integralBound then
    let truncated := Float.ofInt value.toInt64.toInt
    withZeroSign value (if truncated > value then truncated - 1 else truncated)
  else value

/-- The least integral double not below the value ({lit}`ceil`). -/
def ceilDouble (value : Float) : Float :=
  if value.abs < integralBound then
    let truncated := Float.ofInt value.toInt64.toInt
    withZeroSign value (if truncated < value then truncated + 1 else truncated)
  else value

/-- The number of a value as {lit}`sqlite3_value_numeric_type` sees it: text that reads as a
number becomes that number ({name}`numericText`); none for any other value. -/
def numericArgument : Value → Option Value
  | .text bytes => match numericText bytes with
    | number@(.integer _) | number@(.real _) => some number
    | .text _ | .blob _ | .null => none
  | number@(.integer _) | number@(.real _) => some number
  | .blob _ | .null => none

/-- {lit}`floor`, {lit}`ceil` or {lit}`trunc` of a value ({lit}`ceilingFunc`): an integer stays,
a REAL is rounded by {lit}`rounding`, and any other value is NULL. -/
def roundingValue (rounding : Float → Float) (value : Value) : Value :=
  match numericArgument value with
  | some (.integer integer) => .integer integer
  | some (.real bits) => realValue (rounding (Float.ofBits bits))
  | some (.text _) | some (.blob _) | some .null | none => .null

/-- The bytes of a double by {lit}`%!.Nf` with {lit}`digits` digits after the point
({lit}`etFLOAT` with the {lit}`!` flag), without removing trailing zeros, which {name}`atof`
ignores. -/
def fixedText (digits : Nat) (value : Float) : List UInt8 :=
  let (negative, decoded, point) := decodeDouble true value (-(digits : Int))
  (if negative then [45] else []) ++ fixedDigitBytes true decoded point digits

/-- The most digits that {lit}`round` keeps after the point; more digits are clamped to it, as
{lit}`roundFunc` does. -/
def roundDigitLimit : Int := 30

/-- {lit}`round(x [, digits])` ({lit}`roundFunc`): NULL digits or a NULL value give NULL; the
digits are clamped to 0 to {name}`roundDigitLimit`; the double of the value ({lit}`sqlite3_value_double`) stays beyond
{name}`integralBound`, with no digits is truncated after adding or subtracting 0.5, and else is
written by {name}`fixedText` and read back. The result is a REAL. -/
def roundValue (value : Value) (digits : Option Value) : Value :=
  if digits.any (·.isNull) || value.isNull then .null
  else
    let count := match digits with
      | none => 0
      | some digits =>
        let count := digits.toInt64
        if count > roundDigitLimit then roundDigitLimit else if count < 0 then 0 else count
    let double := value.toReal
    if double < -integralBound || double > integralBound then realValue double
    else if count == 0 then realValue (Float.ofInt (double + (if double < 0 then -0.5 else 0.5)).toInt64.toInt)
    else realValue (atof (fixedText count.toNat double)).1

/-- The double nearest to π ({lit}`M_PI`). -/
def piDouble : Float := Float.ofBits 0x400921FB54442D18

/-- A function of one double ({lit}`math1Func`): NULL unless the value is a number or text that
reads as one; a NaN result is NULL. -/
def doubleValue (function : Float → Float) (value : Value) : Value :=
  match numericArgument value with
  | some number => realValue (function number.toReal)
  | none => .null

/-- The sign, the integer significand and the binary exponent of a finite double:
{lit}`value = significand * 2 ^ exponent`. -/
def decomposeDouble (value : Float) : Bool × Nat × Int :=
  let bits := value.toBits.toNat
  let exponent := (bits >>> 52) % 2048
  let fraction := bits % 2 ^ 52
  (bits >>> 63 == 1, if exponent == 0 then fraction else fraction + 2 ^ 52,
    if exponent == 0 then -1074 else (exponent : Int) - 1075)

/-- The double of {lit}`significand * 2 ^ exponent` with the sign, for a value that a double
represents exactly, as the remainder of {lit}`modDouble` is: a normal double, or a subnormal
one below {lit}`2^-1022`. -/
def composeDouble (negative : Bool) (significand : Nat) (exponent : Int) : Float :=
  let sign := if negative then 2 ^ 63 else 0
  if significand == 0 then Float.ofBits (UInt64.ofNat sign)
  else
    let length := Nat.log2 significand + 1
    let top := exponent + length - 1
    if top < -1022 then Float.ofBits (UInt64.ofNat (sign + significand * 2 ^ (exponent + 1074).toNat))
    else
      let mantissa := if length > 53 then significand / 2 ^ (length - 53) else significand * 2 ^ (53 - length)
      Float.ofBits (UInt64.ofNat (sign + (top + 1023).toNat * 2 ^ 52 + (mantissa - 2 ^ 52)))

/-- The exact remainder of {lit}`fmod(x, y)`: {lit}`x - n * y` for the integer {lit}`n` of
{lit}`x / y` truncated toward zero, with the sign of {lit}`x`. NaN for a zero divisor, an infinite
dividend or a NaN; {lit}`x` for an infinite divisor and for {lit}`|x| < |y|`. -/
def modDouble (x y : Float) : Float :=
  if x.isNaN || y.isNaN || x.isInf || y == 0 then 0.0 / 0.0
  else if y.isInf || x == 0 then x
  else
    let (negative, xSignificand, xExponent) := decomposeDouble x
    let (_, ySignificand, yExponent) := decomposeDouble y
    let lowest := min xExponent yExponent
    let dividend := xSignificand * 2 ^ (xExponent - lowest).toNat
    let divisor := ySignificand * 2 ^ (yExponent - lowest).toNat
    composeDouble negative (dividend % divisor) lowest

/-- {lit}`mod(x, y)` ({lit}`math2Func` with {lit}`fmod`): NULL unless both are numbers or text that
reads as one; else the REAL of {name}`modDouble` of their doubles, NULL for a NaN. -/
def modValue (x y : Value) : Value :=
  match numericArgument x, numericArgument y with
  | some x, some y => realValue (modDouble x.toReal y.toReal)
  | some _, none | none, some _ | none, none => .null

end Belay.Sqlite.Model.Resolved
