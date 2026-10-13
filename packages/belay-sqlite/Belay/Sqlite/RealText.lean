import Belay.Sqlite.NumberText

set_option doc.verso true

/-! SQLite's conversion of a REAL to text (ADR 0012, slice 2): {lit}`%!.15g` of its own
printf over {lit}`sqlite3FpDecode`, ported from the pinned 3.51.0 source. The decoding
scales the value into 64 bits in double-double arithmetic, so it is not a correctly
rounded decimal conversion; the model follows its steps. A {lit}`CAST(x AS TEXT)` of a
REAL gives this text. -/

namespace Belay.Sqlite

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

/-- The character of a decimal digit. -/
def digitChar (digit : Nat) : Char := Char.ofNat (48 + digit)

/-- The digit at a position, or 0 past the end, as a character. -/
def digitAt (digits : List Nat) (index : Nat) : Char := digitChar (digits.getD index 0)

/-- The exponent suffix of {lit}`%e`: {lit}`e`, the sign, and two or three digits. -/
def exponentSuffix (exponent : Int) : String :=
  let magnitude := exponent.natAbs
  let hundreds := if magnitude ≥ 100 then String.singleton (digitChar (magnitude / 100)) else ""
  let rest := magnitude % 100
  "e" ++ (if exponent < 0 then "-" else "+") ++ hundreds ++ String.ofList [digitChar (rest / 10), digitChar (rest % 10)]

/-- Remove the trailing zeros of a fixed-point text, and keep one zero after a point
that would end the text, as {lit}`%!g` does. -/
def trimFraction (text : List Char) : List Char :=
  let trimmed := (text.reverse.dropWhile (· == '0')).reverse
  if trimmed.getLast? == some '.' then trimmed ++ ['0'] else trimmed

/-- The significant digits of a REAL as text: the precision 15 of {lit}`%!.15g`. -/
def realTextDigits : Nat := 15

/-- The digit limit of {lit}`sqlite3FpDecode` under the {lit}`!` flag of SQLite's printf:
a decoding with more digits is rounded to it. -/
def realTextDigitLimit : Nat := 26

/-- The least decimal exponent that {lit}`%g` writes in plain notation; below it, the
text uses exponent notation. -/
def plainExponentMinimum : Int := -4

/-- The text of a finite double that is not zero, by {lit}`%!.15g`: {name}`realTextDigits`
significant digits, plain notation for decimal exponents from
{name}`plainExponentMinimum` to one less than the digit count, else exponent notation;
trailing zeros removed, but at least one digit after the point. -/
def finiteText (negative : Bool) (value : Float) : String :=
  let (digits, exponent) := fpDigits value
  let (digits, point) := roundDigits realTextDigits realTextDigitLimit digits (digits.length + exponent)
  let exp := point - 1
  let last : Int := realTextDigits - 1
  let sign := if negative then "-" else ""
  if exp < plainExponentMinimum || exp > last then
    let body := [digitAt digits 0, '.'] ++ (List.range (realTextDigits - 1)).map (fun index => digitAt digits (index + 1))
    sign ++ String.ofList (trimFraction body) ++ exponentSuffix exp
  else
    let precision := (last - exp).toNat
    let whole := if exp < 0 then ['0'] else (List.range (exp.toNat + 1)).map (digitAt digits)
    let used := if exp < 0 then 0 else exp.toNat + 1
    let zeros := min precision (if exp < 0 then (-exp - 1).toNat else 0)
    let fraction := List.replicate zeros '0' ++ (List.range (precision - zeros)).map (fun index => digitAt digits (used + index))
    sign ++ String.ofList (trimFraction (whole ++ ['.'] ++ fraction))

/-- SQLite's text of a REAL ({lit}`vdbeMemRenderNum` with {lit}`%!.15g`): {lit}`0.0` for
either zero, {lit}`Inf` and {lit}`-Inf` for the infinities, else {name}`finiteText`.
SQLite stores no NaN; a NaN gives {lit}`NaN`. -/
def realText (value : Float) : String :=
  if value.isNaN then "NaN"
  else if value == 0 then "0.0"
  else if value.isInf then (if value < 0 then "-Inf" else "Inf")
  else finiteText (value < 0) (if value < 0 then -value else value)

end Belay.Sqlite
