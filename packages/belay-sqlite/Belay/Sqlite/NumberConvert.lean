import Belay.Sqlite.NumberText

set_option doc.verso true

/-! The computing part of SQLite's text-to-number conversions (ADR 0012, slice 2):
{lit}`sqlite3AtoF` after its parse, {lit}`sqlite3Atoi64` and {lit}`sqlite3RealToI64`,
ported from the pinned 3.51.0 source. -/

namespace Belay.Sqlite

/-- A positive infinity, as SQLite gets it from {lit}`1e300*1e300`. -/
def infinity : Float := Float.ofBits 0x7FF0000000000000

/-- Scale the double-double {lit}`x` by {lit}`10^exponent` as {lit}`sqlite3AtoF` does:
steps of {lit}`10^100`, then {lit}`10^10`, then 10, each with its error term. -/
def scaleByTen (x : Float × Float) (exponent : Int) : Float × Float :=
  if exponent ≥ 0 then
    let n := exponent.toNat
    let (x, n) := scaleDown n 100 1.0e100 (-1.5902891109759918046e83) x n
    let (x, n) := scaleDown n 10 1.0e10 0 x n
    (scaleDown n 1 10 0 x n).1
  else
    let n := (-exponent).toNat
    let (x, n) := scaleDown n 100 1.0e-100 (-1.99918998026028836196e-117) x n
    let (x, n) := scaleDown n 10 1.0e-10 (-3.6432197315497741579e-27) x n
    (scaleDown n 1 1.0e-1 (-5.5511151231257827021e-18) x n).1

/-- The significand limit of the normalization in {lit}`sqlite3AtoF`:
{lit}`(LARGEST_UINT64 - 0x7ff) / 10`. Below it, a multiplication by ten keeps the
significand in 64 bits. -/
def atofNormalizeLimit : Nat := (2 ^ 64 - 1 - 0x7ff) / 10

/-- Normalize the significand and the decimal exponent as {lit}`sqlite3AtoF` does
before it scales: multiply by ten while the exponent is positive and the significand
stays below {name}`atofNormalizeLimit`, then divide by ten while the exponent is
negative and the significand ends in a zero. -/
def atofNormalize (significand : Nat) (exponent : Int) : Nat × Int :=
  let rec up (fuel : Nat) (s : Nat) (e : Int) : Nat × Int := match fuel with
    | 0 => (s, e)
    | fuel + 1 => if e > 0 && s < atofNormalizeLimit then up fuel (s * 10) (e - 1) else (s, e)
  let rec down (fuel : Nat) (s : Nat) (e : Int) : Nat × Int := match fuel with
    | 0 => (s, e)
    | fuel + 1 => if e < 0 && s % 10 == 0 then down fuel (s / 10) (e + 1) else (s, e)
  let (s, e) := up exponent.natAbs significand exponent
  down e.natAbs s e

/-- The double that {lit}`sqlite3AtoF` computes from a nonzero significand and a decimal
exponent: the significand as a double with its rounding error, scaled by powers of ten,
then summed. A NaN becomes a positive infinity. -/
def atofMagnitude (significand : Nat) (exponent : Int) : Float :=
  let (s, e) := atofNormalize significand exponent
  let high := (UInt64.ofNat s).toFloat
  let low : Float :=
    if high ≤ 18446744073709549568.0 then
      let rounded := high.toUInt64.toNat
      if s ≥ rounded then (UInt64.ofNat (s - rounded)).toFloat else -(UInt64.ofNat (rounded - s)).toFloat
    else 0
  let (a, b) := scaleByTen (high, low) e
  let sum := a + b
  if sum.isNaN then infinity else sum

/-- SQLite's {lit}`sqlite3AtoF` on UTF-8 text: the double, and the result code. The code
is the number kind (1 for an integer form, 2 or more otherwise) when the whole text is
a number; {lit}`-1` when a prefix with a fraction or exponent is a number; else 0. -/
def atof (bytes : List UInt8) : Float × Int :=
  match atofParse bytes with
  | none => (0, 0)
  | some (sign, state, rest) =>
    let exponent : Int := (if state.negativeExponent then -(state.exponent : Int) else state.exponent) + state.shift
    let magnitude := if state.significand == 0 then 0 else atofMagnitude state.significand exponent
    let value := if sign < 0 then -magnitude else magnitude
    let code : Int :=
      if rest.isEmpty && state.digits > 0 && state.exponentValid then state.kind
      else if state.kind ≥ 2 && (state.kind == 3 || state.exponentValid) && state.digits > 0 then -1
      else 0
    (value, code)

/-- SQLite's {lit}`sqlite3RealToI64`: a double to a 64-bit integer, saturated at the
limits and truncated toward zero. A NaN passes both limit tests and gives the smallest
64-bit integer, as the conversion instruction of x86-64 does; SQLite stores no NaN, so
only an intermediate value can be one. -/
def realToI64 (value : Float) : Int :=
  if value < -9223372036854774784.0 then -(2 ^ 63)
  else if value > 9223372036854774784.0 then 2 ^ 63 - 1
  else if value.isNaN then -(2 ^ 63)
  else if value < 0 then -((-value).toUInt64.toNat : Int)
  else (value.toUInt64.toNat : Int)

/-- Read decimal digits into a 64-bit accumulator that wraps as C's {lit}`u64` does;
also count the digits. -/
def atoiDigits (value count : Nat) : List UInt8 → Nat × Nat × List UInt8
  | byte :: rest =>
    if isDigitByte byte then atoiDigits ((value * 10 + digitValue byte) % 2 ^ 64) (count + 1) rest
    else (value, count, byte :: rest)
  | [] => (value, count, [])

/-- SQLite's {lit}`sqlite3Atoi64` on UTF-8 text: the integer and the result code: -1 when
no digits start the text, 0 when it fits, 1 with other text after the digits, 2 when
the number is too large, 3 for exactly {lit}`9223372036854775808` without a minus. A
number that is too large gives the limit of its sign. -/
def atoi64 (bytes : List UInt8) : Int × Int :=
  let (sign, text) := readSign (dropSpaces bytes)
  let negative := sign < 0
  let afterZeros := text.dropWhile (· == 48)
  let (u, count, rest) := atoiDigits 0 0 afterZeros
  let value : Int := if u > 2 ^ 63 - 1 then (if negative then -(2 ^ 63) else 2 ^ 63 - 1)
    else if negative then -(u : Int) else u
  let base : Int := if count == 0 && afterZeros.length == text.length then -1
    else if !(dropSpaces rest).isEmpty then 1 else 0
  if count < 19 then (value, base)
  else
    let digits := (afterZeros.take 19).map digitValue
    let pow63 := [9, 2, 2, 3, 3, 7, 2, 0, 3, 6, 8, 5, 4, 7, 7, 5, 8, 0, 8]
    let order := if count > 19 then Ordering.gt else compare digits pow63
    match order with
    | .lt => (value, base)
    | .gt => (if negative then -(2 ^ 63) else 2 ^ 63 - 1, 2)
    | .eq => if negative then (-(2 ^ 63), base) else (2 ^ 63 - 1, 3)

end Belay.Sqlite
