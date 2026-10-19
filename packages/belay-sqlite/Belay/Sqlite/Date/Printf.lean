import Belay.Sqlite.RealText

set_option doc.verso true

/-! The conversions of SQLite's own printf ({lit}`sqlite3_str_vappendf` of the pinned
3.51.0 source) that {lit}`strftimeFunc` uses (ADR 0012, amendment 5, slice 6f), over the
front end of {lit}`RealText.lean`: {lit}`%d` with a width, with or without zeros,
{lit}`%lld`, {lit}`%.3f`, {lit}`%06.3f` and {lit}`%.16g`. The floating-point conversions
use {lit}`sqlite3FpDecode` without the {lit}`!` flag, so they round to at most 16
significant digits. Every double that {lit}`strftimeFunc` formats is finite; the port
has no branch for NaN or infinity. -/

namespace Belay.Sqlite

/-- The bytes of the decimal digits of a natural number, most significant first. -/
def decimalDigitBytes (value : Nat) : List UInt8 := (decimalDigits value).map digitByte

/-- An integer by {lit}`%Wd`, {lit}`%0Wd` or {lit}`%lld` (width 0): a minus for a
negative number, the digits of its magnitude, and padding to the width. With
{lit}`zeroPad` the zeros go after the sign; else spaces go before it. -/
def formatInteger (width : Nat) (zeroPad : Bool) (value : Int) : List UInt8 :=
  let digits := decimalDigitBytes value.natAbs
  let sign : List UInt8 := if value < 0 then [45] else []
  let precision := if zeroPad then width - sign.length else 0
  let body := sign ++ List.replicate (precision - digits.length) 48 ++ digits
  List.replicate (width - body.length) 32 ++ body

/-- A double by {lit}`%.Pf` or {lit}`%0W.Pf`: the sign, then {name}`fixedDigitBytes`
after rounding to {lit}`precision` digits after the point. With {lit}`zeroPad`, zeros
after the sign fill the text to the width. -/
def formatFixed (width : Nat) (zeroPad : Bool) (precision : Nat) (value : Float) : List UInt8 :=
  let (negative, digits, point) := decodeDouble Bool.false value (-(precision : Int))
  let sign : List UInt8 := if negative then [45] else []
  let body := fixedDigitBytes Bool.false digits point precision
  let padding := if zeroPad then width - (sign.length + body.length) else 0
  sign ++ List.replicate padding 48 ++ body

/-- The significant digits of {lit}`%.16g`, which {lit}`strftime` uses for {lit}`%J`. -/
def julianDayTextDigits : Nat := 16

end Belay.Sqlite
