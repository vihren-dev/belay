import Belay.Sqlite.Model.NumberText
import Belay.Sqlite.Model.ByteText

set_option doc.verso true

/-! The floating-point conversions of SQLite's own printf ({lit}`sqlite3_str_vappendf` of
the pinned 3.51.0 source) over {lit}`sqlite3FpDecode`, as bytes, and the text of a REAL
(ADR 0012, slice 2): {lit}`%!.15g`. The decoding scales the value into 64 bits in
double-double arithmetic, so it is not a correctly rounded decimal conversion; the model
follows its steps. A {lit}`CAST(x AS TEXT)` of a REAL gives this text. The date functions
use the same conversions for {lit}`%.3f` and {lit}`%.16g` ({lit}`Date/Printf.lean`). -/

namespace Belay.Sqlite.Model

/-- The decimal digits of a natural number, most significant first; {lean}`[0]` for 0. -/
def decimalDigits (value : Nat) : List Nat := (Nat.toDigits 10 value).map fun c => c.toNat - 48

/-- Repeat {name}`dekkerMul2` with one factor while {lit}`continues` holds for the high
part, and count the steps; the fuel bounds them. -/
def scaleWhile (fuel : Nat) (continues : Float → Bool) (y yy : Float) (x : Float × Float) (steps : Nat) :
    (Float × Float) × Nat :=
  match fuel with
  | 0 => (x, steps)
  | fuel + 1 => if continues x.1 then scaleWhile fuel continues y yy (dekkerMul2 x y yy) (steps + 1) else (x, steps)

/-- The bound on scaling steps: enough for every finite double. -/
def scaleFuel : Nat := 400

/-- The decimal digits and the decimal exponent of a positive finite double, as
{lit}`sqlite3FpDecode` gets them before rounding: the value scaled into the range near
{lit}`2^63` in double-double steps, then read as an unsigned 64-bit integer. The value is
the digits times {lit}`10^exponent`. -/
def fpDigits (value : Float) : List Nat × Int :=
  let large := 9.223372036854774784e18
  let (x, exponent) : (Float × Float) × Int :=
    if value > large then
      let (x, a) := scaleWhile scaleFuel (· > 9.223372036854774784e118) 1.0e-100 (-1.99918998026028836196e-117) (value, 0) 0
      let (x, b) := scaleWhile scaleFuel (· > 9.223372036854774784e28) 1.0e-10 (-3.6432197315497741579e-27) x 0
      let (x, c) := scaleWhile scaleFuel (· > large) 1.0e-1 (-5.5511151231257827021e-18) x 0
      (x, (100 * a + 10 * b + c : Nat))
    else
      let (x, a) := scaleWhile scaleFuel (· < 9.223372036854774784e-83) 1.0e100 (-1.5902891109759918046e83) (value, 0) 0
      let (x, b) := scaleWhile scaleFuel (· < 9.223372036854774784e7) 1.0e10 0 x 0
      let (x, c) := scaleWhile scaleFuel (· < 9.22337203685477478e17) 10 0 x 0
      (x, -((100 * a + 10 * b + c : Nat) : Int))
  let high := x.1.toUInt64.toNat
  let integer := if x.2 < 0 then high - (-x.2).toUInt64.toNat else high + x.2.toUInt64.toNat
  (decimalDigits integer, exponent)

/-- Add one to a list of decimal digits, most significant first: the digits and whether
a carry leaves the first digit. -/
def incrementDigits : List Nat → List Nat × Bool
  | [] => ([], true)
  | digit :: rest =>
    let (rest, carry) := incrementDigits rest
    if !carry then (digit :: rest, false)
    else if digit + 1 ≤ 9 then ((digit + 1) :: rest, false) else (0 :: rest, true)

/-- Round decimal digits to {lit}`round` significant digits as {lit}`sqlite3FpDecode`
does for a positive {lit}`round`, then drop trailing zeros: the digits and the position
of the decimal point after the first digit ({lit}`iDP`). A carry out of the first digit
adds a leading 1. -/
def roundDigits (round maximum : Nat) (digits : List Nat) (point : Int) : List Nat × Int :=
  let (digits, point) :=
    if round > 0 && (round < digits.length || digits.length > maximum) then
      let round := min round maximum
      let kept := digits.take round
      if digits.getD round 0 ≥ 5 then
        match incrementDigits kept with
        | (kept, false) => (kept, point)
        | (kept, true) => (1 :: kept, point + 1)
      else (kept, point)
    else (digits, point)
  let trimmed := (digits.reverse.dropWhile (· == 0)).reverse
  (if trimmed.isEmpty then [0] else trimmed, point)

/-- The greatest number of significant digits of {lit}`sqlite3FpDecode`: 26 under the
{lit}`!` flag of SQLite's printf ({lit}`alternate`), else 16. A decoding with more digits
is rounded to it. -/
def printfDigitLimit (alternate : Bool) : Nat := if alternate then 26 else 16

/-- {lit}`sqlite3FpDecode` of a double: its sign, its significant digits and the position
of the decimal point after the first digit ({lit}`iDP`). A positive {lit}`round` keeps
that many significant digits; zero or less keeps {lit}`-round` digits after the decimal
point. {lit}`alternate` is the {lit}`!` flag ({name}`printfDigitLimit`). Zero gives the
digit 0 and the point 1. -/
def decodeDouble (alternate : Bool) (value : Float) (round : Int) : Bool × List Nat × Int :=
  if value == 0 then (false, [0], 1) else
  let negative := value < 0
  let (digits, exponent) := fpDigits (if negative then -value else value)
  let point : Int := digits.length + exponent
  let (digits, point, round) :=
    if round > 0 then (digits, point, round) else
    let round := point - round
    if round == 0 && digits.headD 0 ≥ 5 then (0 :: digits, point + 1, 1) else (digits, point, round)
  let (digits, point) := roundDigits round.toNat (printfDigitLimit alternate) digits point
  (negative, digits, point)

/-- The ASCII byte of a decimal digit. -/
def digitByte (digit : Nat) : UInt8 := (48 + digit).toUInt8

/-- The fixed-point bytes of decoded digits with {lit}`precision` digits after the
point, as the {lit}`etFLOAT` branch writes them: the integer digits (or one zero), the
point when the precision is positive or {lit}`forcePoint` holds ({lit}`flag_dp`), zeros
before the first significant digit, then the digits, with zeros past the last one. -/
def fixedDigitBytes (forcePoint : Bool) (digits : List Nat) (point : Int) (precision : Nat) : List UInt8 :=
  let byteAt := fun (index : Nat) => digitByte (digits.getD index 0)
  let whole := if point ≤ 0 then [48] else (List.range point.toNat).map byteAt
  let used := if point ≤ 0 then 0 else point.toNat
  let zeros := min precision (if point < 0 then (-point).toNat else 0)
  let fraction := List.replicate zeros 48 ++ (List.range (precision - zeros)).map (fun index => byteAt (used + index))
  whole ++ (if precision > 0 || forcePoint then 46 :: fraction else [])

/-- Remove the trailing zeros after a point, as {lit}`%g` does ({lit}`flag_rtz`). A point
that would end the text is removed, or keeps one zero under the {lit}`!` flag
({lit}`alternate`). A text without a point stays. -/
def trimGeneralFraction (alternate : Bool) (bytes : List UInt8) : List UInt8 :=
  if !bytes.contains 46 then bytes else
  let trimmed := (bytes.reverse.dropWhile (· == 48)).reverse
  if trimmed.getLast? == some 46 then (if alternate then trimmed ++ [48] else trimmed.dropLast) else trimmed

/-- The exponent suffix of {lit}`%e` as bytes: {lit}`e`, the sign, and two or three
digits. -/
def exponentSuffixBytes (exponent : Int) : List UInt8 :=
  let magnitude := exponent.natAbs
  let hundreds := if magnitude ≥ 100 then [digitByte (magnitude / 100)] else []
  [101, if exponent < 0 then 45 else 43] ++ hundreds ++ [digitByte (magnitude % 100 / 10), digitByte (magnitude % 10)]

/-- The least decimal exponent that {lit}`%g` writes in plain notation; below it, the
text uses exponent notation. -/
def plainExponentMinimum : Int := -4

/-- A double by {lit}`%.Pg` ({lit}`etGENERIC`), or {lit}`%!.Pg` when {lit}`alternate`
holds: {lit}`precision` significant digits, plain notation for a decimal exponent from
{name}`plainExponentMinimum` to one less than the precision, else exponent notation,
then {name}`trimGeneralFraction`. Under the {lit}`!` flag the text always has a point.
For example {lean}`formatGeneral 16 false 2.5` is the bytes of {lit}`2.5`. -/
def formatGeneral (precision : Nat) (alternate : Bool) (value : Float) : List UInt8 :=
  let (negative, digits, point) := decodeDouble alternate value precision
  let sign : List UInt8 := if negative then [45] else []
  let exponent := point - 1
  let last : Int := precision - 1
  if exponent < plainExponentMinimum || exponent > last then
    sign ++ trimGeneralFraction alternate (fixedDigitBytes alternate digits 1 (precision - 1)) ++
      exponentSuffixBytes exponent
  else sign ++ trimGeneralFraction alternate (fixedDigitBytes alternate digits point (last - exponent).toNat)

/-- The significant digits of a REAL as text: the precision 15 of {lit}`%!.15g`. -/
def realTextDigits : Nat := 15

/-- SQLite's text of a REAL as bytes ({lit}`vdbeMemRenderNum` with {lit}`%!.15g`):
{lit}`0.0` for either zero, {lit}`Inf` and {lit}`-Inf` for the infinities, else
{name}`formatGeneral` with {name}`realTextDigits` digits and the {lit}`!` flag. SQLite
stores no NaN; a NaN gives {lit}`NaN`. -/
def realText (value : Float) : List UInt8 :=
  if value.isNaN then bytes! "NaN"
  else if value == 0 then bytes! "0.0"
  else if value.isInf then (if value < 0 then bytes! "-Inf" else bytes! "Inf")
  else formatGeneral realTextDigits true value

end Belay.Sqlite.Model
