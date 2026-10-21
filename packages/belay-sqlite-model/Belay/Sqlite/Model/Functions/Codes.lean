import Belay.Sqlite.Model.Functions.Text

set_option doc.verso true

/-! The functions of ADR 0015, slice 1, that read or write bytes and code points, ported from
SQLite 3.51.0's {lit}`func.c`: {lit}`hex`, {lit}`unhex`, {lit}`char`, {lit}`unicode` and
{lit}`unistr`. -/

namespace Belay.Sqlite.Model.Resolved

/-- An upper-case hexadecimal digit of a nibble. -/
def hexDigit (nibble : UInt8) : UInt8 := if nibble < 10 then 48 + nibble else 55 + nibble

/-- {lit}`hex(x)` ({lit}`hexFunc`): two upper-case hexadecimal digits for each byte of the value
as a BLOB or text; NULL gives empty text. -/
def hexValue (value : Value) : Value :=
  .text (value.textBytes.flatMap fun (byte : UInt8) => [hexDigit (byte >>> 4), hexDigit (byte &&& 15)])

/-- The value of a hexadecimal digit, or none. -/
def hexDigitValue (byte : UInt8) : Option UInt8 :=
  if 48 ≤ byte && byte ≤ 57 then some (byte - 48)
  else if 65 ≤ byte && byte ≤ 70 then some (byte - 55)
  else if 97 ≤ byte && byte ≤ 102 then some (byte - 87)
  else none

/-- The bytes of the hexadecimal digit pairs of a C string, skipping the code points of
{lit}`skip` between pairs ({lit}`unhexFunc`); none for an odd digit or another character. The
fuel bounds the steps. -/
def unhexBytes (skip : List UInt32) : Nat → List UInt8 → Option (List UInt8)
  | 0, _ => some []
  | _, [] => some []
  | fuel + 1, text@(high :: rest) => match hexDigitValue high with
    | some upper => match rest with
      | low :: after => match hexDigitValue low with
        | some lower => (((upper <<< 4) ||| lower) :: ·) <$> unhexBytes skip fuel after
        | none => none
      | [] => none
    | none =>
      let (character, after) := utf8Read text
      if skip.contains character then unhexBytes skip fuel after else none

/-- {lit}`unhex(x [, ignored])` ({lit}`unhexFunc`): the BLOB of the hexadecimal digit pairs of the C
string {lit}`x`; a character of {lit}`ignored` between pairs is skipped. A NULL argument, an odd
digit, or another character gives NULL. -/
def unhexValue (value : Value) (ignored : Option Value) : Value :=
  if value.isNull || ignored.any (·.isNull) then .null
  else
    let skip := ((ignored.map fun pass => utf8Characters pass.textBytes.length pass.textBytes).getD []).map
      fun character => (utf8Read character).1
    let bytes := bytesBeforeNul value.textBytes
    match unhexBytes skip bytes.length bytes with
    | some blob => .blob blob
    | none => .null

/-- {lit}`char(x, ...)` ({lit}`charFunc`): the text of the code points of the integer values, with
{lit}`U+FFFD` for a value below 0 or above {lit}`0x10FFFF`. -/
def charValue (values : List Value) : Value :=
  .text (values.flatMap fun value =>
    let code := value.toInt64
    utf8Bytes (if code < 0 || code > 0x10FFFF then 0xFFFD else code.toNat.toUInt32))

/-- {lit}`unicode(x)` ({lit}`unicodeFunc`): the code point of the first character of the C string,
NULL for NULL and for empty text. -/
def unicodeValue (value : Value) : Value :=
  if value.isNull then .null
  else match bytesBeforeNul value.textBytes with
    | [] => .null
    | bytes => .integer (utf8Read bytes).1.toNat

/-- Whether the next {lit}`count` bytes are hexadecimal digits, with their value. -/
def hexCode (count : Nat) (bytes : List UInt8) : Option UInt32 :=
  let digits := bytes.take count
  if digits.length != count then none
  else digits.foldlM (fun code byte => (hexDigitValue byte).map fun digit => code * 16 + digit.toUInt32) 0

/-- The bytes with their Unicode escapes replaced ({lit}`unistrFunc`): {lit}`\\\\`, {lit}`\\XXXX`,
{lit}`\\uXXXX`, {lit}`\\+XXXXXX` and {lit}`\\UXXXXXXXX`, before the first NUL; none for another
backslash. The fuel bounds the steps. -/
def unistrBytes : Nat → List UInt8 → Option (List UInt8)
  | 0, text => some text
  | _, [] => some []
  | fuel + 1, byte :: rest =>
    if byte == 0 then some (byte :: rest)
    else if byte != 92 then (byte :: ·) <$> unistrBytes fuel rest
    else match rest with
      | 92 :: after => (92 :: ·) <$> unistrBytes fuel after
      | 43 :: after => (hexCode 6 after).bind fun code => (utf8Bytes code ++ ·) <$> unistrBytes fuel (after.drop 6)
      | 117 :: after => (hexCode 4 after).bind fun code => (utf8Bytes code ++ ·) <$> unistrBytes fuel (after.drop 4)
      | 85 :: after => (hexCode 8 after).bind fun code => (utf8Bytes code ++ ·) <$> unistrBytes fuel (after.drop 8)
      | after => (hexCode 4 after).bind fun code => (utf8Bytes code ++ ·) <$> unistrBytes fuel (after.drop 4)

/-- {lit}`unistr(x)` ({lit}`unistrFunc`): the text with its escapes replaced: {lit}`\\` by a backslash,
and {lit}`\XXXX`, {lit}`\uXXXX`, {lit}`\+XXXXXX` and {lit}`\UXXXXXXXX` by the UTF-8 bytes of the code
point. Escapes count only before the first NUL; the bytes after it stay. NULL gives NULL, and
any other backslash fails with {lit}`invalid Unicode escape` (none). -/
def unistrValue (value : Value) : Option Value :=
  if value.isNull then some .null
  else
    let bytes := value.textBytes
    (Value.text ·) <$> unistrBytes bytes.length bytes

end Belay.Sqlite.Model.Resolved
