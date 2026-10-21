import Belay.Sqlite.Model.RealText
import Belay.Sqlite.Model.NumberConvert
import Belay.Sqlite.Model.ByteText
import Belay.Sqlite.Model.Functions.Codes

set_option doc.verso true

/-! {lit}`quote` and {lit}`unistr_quote` (ADR 0015, slice 1): SQLite 3.51.0's {lit}`sqlite3QuoteValue`,
which writes a value as an SQL literal with the printf conversions {lit}`%!0.15g`,
{lit}`%!0.20e`, {lit}`%lld` and {lit}`%Q` or {lit}`%#Q`. -/

namespace Belay.Sqlite.Model.Resolved

/-- The text of an infinity under the {lit}`0` flag of printf: {lit}`9.0e+999`, with a minus sign
for negative infinity, as {lit}`sqlite3FpDecode` gives it the digit 9 and the point 1000. -/
def infinityText (negative : Bool) : List UInt8 :=
  (if negative then [45] else []) ++ "9.0e+999".toUTF8.toList

/-- A double by {lit}`%!0.Pe` ({lit}`etEXP` with the {lit}`!` and {lit}`0` flags): one digit, the
point, {lit}`precision` digits with the trailing zeros removed ({lit}`flag_rtz` under {lit}`!`), and the
exponent. -/
def exponentText (precision : Nat) (value : Float) : List UInt8 :=
  if value.isInf then infinityText (value < 0)
  else
    let (negative, digits, point) := decodeDouble true value (precision + 1)
    (if negative then [45] else []) ++ trimGeneralFraction true (fixedDigitBytes true digits 1 precision) ++
      exponentSuffixBytes (point - 1)

/-- A REAL as {lit}`quote` writes it: {lit}`%!0.15g` when that text reads back as the same double,
else {lit}`%!0.20e`. For example, 0.1 is {lit}`0.1` and 1/3 is {lit}`3.333333333333333148e-01`. -/
def quoteReal (value : Float) : List UInt8 :=
  let short := if value.isInf then infinityText (value < 0) else formatGeneral 15 true value
  if (atof short).1 != value then exponentText 20 value else short

/-- Text as {lit}`%Q` writes it, with single quotes doubled and around the text; with
{lit}`escape` ({lit}`%#Q`) and a control character ({lit}`0x00` to {lit}`0x1F`) in the text, as
{lit}`unistr('...')` with each backslash doubled and each control character as {lit}`\u00XX`. -/
def quoteText (escape : Bool) (bytes : List UInt8) : List UInt8 :=
  let plain := [39] ++ bytes.flatMap (fun byte => if byte == 39 then [39, 39] else [byte]) ++ [39]
  if !escape || !bytes.any (· ≤ 0x1F) then plain
  else
    let lowerHex := fun (nibble : UInt8) => if nibble < 10 then 48 + nibble else 87 + nibble
    "unistr('".toUTF8.toList ++ bytes.flatMap (fun byte =>
      if byte == 39 then [39, 39] else if byte == 92 then [92, 92]
      else if byte ≤ 0x1F then [92, 117, 48, 48, if byte ≥ 0x10 then 49 else 48, lowerHex (byte &&& 15)]
      else [byte]) ++ [39, 41]

/-- {lit}`quote(x)`, or {lit}`unistr_quote(x)` with {lit}`escape` ({lit}`sqlite3QuoteValue`): a REAL by
{name}`quoteReal`, an integer in decimal, a BLOB as {lit}`X'..'` with upper-case digits, text by
{name}`quoteText` up to its first NUL, NULL as {lit}`NULL`. -/
def quoteValue (escape : Bool) : Value → Value
  | .real bits => .text (quoteReal (Float.ofBits bits))
  | value@(.integer _) => .text value.textBytes
  | .blob bytes => .text ([88, 39] ++ (hexValue (.blob bytes)).textBytes ++ [39])
  | .text bytes => .text (quoteText escape (bytesBeforeNul bytes))
  | .null => .text "NULL".toUTF8.toList

end Belay.Sqlite.Model.Resolved
