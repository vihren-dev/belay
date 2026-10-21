import Belay.Sqlite.Model.RealText

set_option doc.verso true

/-! The number fields of SQLite's {lit}`printf` (ADR 0015, slice 6): the integer conversions
{lit}`%d`, {lit}`%i`, {lit}`%u`, {lit}`%r`, {lit}`%x`, {lit}`%X`, {lit}`%o` and {lit}`%p`, and the
double conversions {lit}`%f`, {lit}`%e`, {lit}`%E`, {lit}`%g` and {lit}`%G`, from the
{lit}`etDECIMAL`, {lit}`etRADIX`, {lit}`etORDINAL`, {lit}`etPOINTER`, {lit}`etFLOAT`, {lit}`etEXP` and
{lit}`etGENERIC` branches of {lit}`sqlite3_str_vappendf` in SQLite 3.51.0. -/

namespace Belay.Sqlite.Model.Resolved

/-- The flags, width and precision of one {lit}`printf` field. -/
structure PrintfSpec where
  /-- The {lit}`-` flag, or a negative {lit}`*` width: pad on the right. -/
  leftJustify : Bool := false
  /-- The {lit}`+` or space flag: the byte before a number that is not negative, or 0. -/
  signFlag : UInt8 := 0
  /-- The {lit}`#` flag. -/
  alternate : Bool := false
  /-- The {lit}`!` flag. -/
  bang : Bool := false
  /-- The {lit}`0` flag. -/
  zeroPad : Bool := false
  /-- The {lit}`,` flag: commas between groups of three digits. -/
  thousands : Bool := false
  /-- The field width in bytes. -/
  width : Nat := 0
  /-- The precision, or none when the field has none. -/
  precision : Option Nat := none
  deriving Repr

/-- The form of an integer conversion: its base, whether it reads a signed value, whether its
digits are capital letters, whether it adds an English ordinal suffix ({lit}`%r`), its
{lit}`#` prefix, and whether the {lit}`,` flag applies. -/
structure IntegerForm where
  /-- The base of the digits. -/
  base : Nat
  /-- Whether the value is signed ({lit}`FLAG_SIGNED`). -/
  signed : Bool
  /-- Whether the digits above 9 are capital letters. -/
  upper : Bool
  /-- Whether the conversion is {lit}`%r`. -/
  ordinal : Bool
  /-- The prefix of the {lit}`#` flag: {lit}`0x`, {lit}`0X` or {lit}`0`. -/
  altPrefix : List UInt8
  /-- Whether the {lit}`,` flag applies (decimal conversions only). -/
  grouped : Bool

/-- The digits of a natural number in a base, most significant first. -/
def baseDigits (form : IntegerForm) (value : Nat) : List UInt8 :=
  (Nat.toDigits form.base value).map fun char =>
    let byte := char.toNat.toUInt8
    if form.upper && 97 ≤ byte then byte - 32 else byte

/-- The suffix of {lit}`%r`: {lit}`st`, {lit}`nd` and {lit}`rd` after 1, 2 and 3 except in the
teens, else {lit}`th`. -/
def ordinalSuffix (value : Nat) : List UInt8 :=
  let last := value % 10
  if last ≥ 4 || last == 0 || value / 10 % 10 == 1 then [116, 104]
  else if last == 1 then [115, 116] else if last == 2 then [110, 100] else [114, 100]

/-- Bytes with a comma before each group of three from the right, as the {lit}`,` flag writes
the digits of an integer. -/
def groupThousands (bytes : List UInt8) : List UInt8 :=
  let length := bytes.length
  bytes.zipIdx.flatMap fun (byte, index) =>
    if index > 0 && (length - index) % 3 == 0 then [44, byte] else [byte]

/-- An integer field ({lit}`etDECIMAL`, {lit}`etRADIX`, {lit}`etORDINAL`): the magnitude, or the
64-bit pattern of an unsigned conversion; the sign of a negative signed value, else the sign
flag of a signed one; with the {lit}`0` flag the precision grows to the width less the sign;
zeros up to the precision; the commas; then the sign and the {lit}`#` prefix of a value that
is not zero. -/
def integerField (spec : PrintfSpec) (form : IntegerForm) (value : Int) : List UInt8 :=
  let (magnitude, sign) : Nat × List UInt8 :=
    if form.signed then
      (if value < 0 then (value.natAbs, [45]) else (value.toNat, if spec.signFlag == 0 then [] else [spec.signFlag]))
    else ((value % 2 ^ 64).toNat, [])
  let precision : Int := match spec.precision with
    | some precision => precision
    | none => -1
  let precision := if spec.zeroPad && precision < (spec.width : Int) - sign.length then (spec.width : Int) - sign.length
    else precision
  let body := baseDigits form magnitude ++ (if form.ordinal then ordinalSuffix magnitude else [])
  let body := List.replicate (precision - body.length).toNat 48 ++ body
  let body := if spec.thousands && form.grouped then groupThousands body else body
  (if spec.alternate && magnitude != 0 then form.altPrefix else []) ++ sign ++ body

/-- The form of a double conversion. -/
inductive DoubleForm where
  /-- {lit}`%f`. -/
  | fixed
  /-- {lit}`%e` or {lit}`%E`. -/
  | exponent
  /-- {lit}`%g` or {lit}`%G`. -/
  | general
  deriving DecidableEq

/-- The digits before the point of a fixed form: one zero for a value below 1, else the digit
at each place, zero past the decoded digits, with a comma under the {lit}`,` flag before each
group of three places. -/
def wholePart (thousands : Bool) (digits : List Nat) (places : Int) : List UInt8 :=
  if places < 0 then [48]
  else (List.range (places.toNat + 1)).flatMap fun index =>
    let left := places.toNat - index
    digitByte (digits.getD index 0) :: (if thousands && left % 3 == 0 && left > 1 then [44] else [])

/-- The text of a finite double or an infinity under the {lit}`0` flag, after the sign
({lit}`etFLOAT`, {lit}`etEXP` and {lit}`etGENERIC` once {lit}`sqlite3FpDecode` gave the digits and
the point): {lit}`%g` picks the exponent or the fixed form and removes trailing zeros. -/
def doubleDigits (spec : PrintfSpec) (form : DoubleForm) (upper : Bool) (precision : Nat) (digits : List Nat)
    (point : Int) : List UInt8 :=
  let exponent := point - 1
  let (form, precision, trim) := match form with
    | .general =>
      let precision := precision - 1
      if exponent < -4 || exponent > precision then (DoubleForm.exponent, precision, !spec.alternate)
      else (DoubleForm.fixed, (precision - exponent).toNat, !spec.alternate)
    | .fixed => (DoubleForm.fixed, precision, spec.bang)
    | .exponent => (DoubleForm.exponent, precision, spec.bang)
  let places := if form == .exponent then 0 else exponent
  let used := if places < 0 then 0 else places.toNat + 1
  let point := precision > 0 || spec.alternate || spec.bang
  let zeros := if places < 0 then min precision (-places - 1).toNat else 0
  let fraction := List.replicate zeros 48 ++
    (List.range (precision - zeros)).map fun index => digitByte (digits.getD (used + index) 0)
  let text := wholePart spec.thousands digits places ++ (if point then 46 :: fraction else [])
  let text := if trim && point then
      let trimmed := (text.reverse.dropWhile (· == 48)).reverse
      if trimmed.getLast? == some 46 then (if spec.bang then trimmed ++ [48] else trimmed.dropLast) else trimmed
    else text
  if form == .exponent then
    let magnitude := exponent.natAbs
    text ++ [if upper then 69 else 101, if exponent < 0 then 45 else 43] ++
      (if magnitude ≥ 100 then [digitByte (magnitude / 100)] else []) ++
      [digitByte (magnitude % 100 / 10), digitByte (magnitude % 10)]
  else text

/-- A double field: the default precision 6, at least 1 for {lit}`%g`; NaN as {lit}`NaN`, or
{lit}`null` under the {lit}`0` flag; an infinity as {lit}`Inf` with its sign or the sign flag, or
under the {lit}`0` flag as the digit 9 at the 1000th place; else the decoded digits
({name}`decodeDouble` with SQLite's rounding place), the sign ({lit}`-` but not for a zero
{lit}`%#f`, else the sign flag) and {name}`doubleDigits`; with the {lit}`0` flag and no {lit}`-`,
zeros after the sign up to the width. -/
def doubleField (spec : PrintfSpec) (form : DoubleForm) (upper : Bool) (value : Float) : List UInt8 :=
  let precision := spec.precision.getD 6
  let precision := if form == .general && precision == 0 then 1 else precision
  let round : Int := match form with
    | .fixed => -(precision : Int)
    | .general => precision
    | .exponent => precision + 1
  let flagSign : List UInt8 := if spec.signFlag == 0 then [] else [spec.signFlag]
  if value.isNaN then if spec.zeroPad then "null".toUTF8.toList else "NaN".toUTF8.toList
  else if value.isInf && !spec.zeroPad then (if value < 0 then [45] else flagSign) ++ "Inf".toUTF8.toList
  else
    let (negative, digits, point) :=
      if value.isInf then (decide (value < 0), [9], (1000 : Int)) else decodeDouble spec.bang value round
    let sign : List UInt8 := if negative then
        (if spec.alternate && spec.signFlag == 0 && form == .fixed && point ≤ round then [] else [45])
      else flagSign
    let text := sign ++ doubleDigits spec form upper precision digits point
    if spec.zeroPad && !spec.leftJustify && text.length < spec.width then
      sign ++ List.replicate (spec.width - text.length) 48 ++ text.drop sign.length
    else text

end Belay.Sqlite.Model.Resolved
