import Belay.Sqlite.Arithmetic
import Belay.Sqlite.ByteText
import Belay.Sqlite.Functions.Utf8
import Belay.Sqlite.Resolution.ScalarFunction

set_option doc.verso true

/-! The text functions of ADR 0015, slice 1, ported from SQLite 3.51.0's {lit}`func.c` over byte
lists: {lit}`lower`, {lit}`upper`, {lit}`substr`, {lit}`instr`, {lit}`replace`, the {lit}`trim`
family, {lit}`hex`, {lit}`unhex`, {lit}`char`, {lit}`unicode`, {lit}`unistr`, {lit}`concat` and
{lit}`concat_ws`. Each function reads its arguments as SQLite's C functions do: some read all
the bytes of a value ({lit}`sqlite3_value_bytes`), others a C string that ends at the first
NUL. -/

namespace Belay.Sqlite.Resolved

/-- An ASCII letter in lower case ({lit}`sqlite3Tolower`); other bytes stay. -/
def lowerByte (byte : UInt8) : UInt8 := if 65 ≤ byte && byte ≤ 90 then byte + 32 else byte

/-- An ASCII letter in upper case ({lit}`sqlite3Toupper`); other bytes stay. -/
def upperByte (byte : UInt8) : UInt8 := if 97 ≤ byte && byte ≤ 122 then byte - 32 else byte

/-- The text of a value with its bytes mapped, as {lit}`lower` and {lit}`upper` do over all
the bytes of the value as text; NULL stays NULL. -/
def mapText (change : UInt8 → UInt8) : Value → Value
  | .null => .null
  | value@(.integer _) | value@(.real _) | value@(.text _) | value@(.blob _) => .text (value.textBytes.map change)

/-- {lit}`substr(x, start [, count])` ({lit}`substrFunc`): characters of text before its first NUL,
or bytes of a BLOB. A positive start counts from 1, a negative one from the end, and a zero
start takes one character less; a negative count takes the characters before the start. A
NULL value, a NULL count, a NULL start of 0, and an empty BLOB, which SQLite reads as no pointer, give
NULL. Without a count, the count is
SQLite's length limit, {lit}`1000000000`. -/
def substrValue (value start : Value) (count : Option Value) : Value :=
  if value.isNull || value == .blob [] then .null
  else if count.any (·.isNull) then .null
  else if start.isNull then .null
  else
    let blob := value matches .blob _
    let bytes := if blob then value.textBytes else bytesBeforeNul value.textBytes
    let p1 := start.toInt64
    let p2 := (count.map Value.toInt64).getD 1000000000
    let length : Int := if blob then bytes.length else if p1 < 0 then
      (bytes.filter fun byte => byte &&& 0xC0 != 0x80).length else 0
    let (p1, p2) :=
      if p1 < 0 then
        let p1 := p1 + length
        if p1 < 0 then (0, if p2 < 0 then 0 else p2 + p1) else (p1, p2)
      else if p1 > 0 then (p1 - 1, p2)
      else (p1, if p2 > 0 then p2 - 1 else p2)
    let (p1, p2) := if p2 < 0 then (if p2 < -p1 then (0, p1) else (p1 + p2, -p2)) else (p1, p2)
    if blob then
      let length := bytes.length
      if p1 ≥ length then .blob [] else .blob ((bytes.drop p1.toNat).take p2.toNat)
    else
      let skip := fun (count : Nat) (text : List UInt8) =>
        (List.range (min count text.length)).foldl (fun rest _ => utf8Skip rest) text
      let from_ := skip p1.toNat bytes
      let rest := skip p2.toNat from_
      .text (from_.take (from_.length - rest.length))

/-- The 1-based position of the first occurrence of the needle ({lit}`instrFunc`), counted in
characters for text and in bytes when both are BLOBs, 1 for an empty needle, 0 when it does not
occur, and NULL when an argument is NULL. Text compares all the bytes of the values; a BLOB
and a text compare as text. The fuel is the length of the haystack. -/
def instrValue (haystack needle : Value) : Value :=
  if haystack.isNull || needle.isNull then .null
  else
    let blobs := (haystack matches .blob _) && (needle matches .blob _)
    let needleBytes := needle.textBytes
    let rec search : List UInt8 → Nat → Nat → Nat
      | text, position, 0 => if needleBytes.isPrefixOf text then position else 0
      | text, position, fuel + 1 =>
        if needleBytes.length > text.length then 0
        else if needleBytes.isPrefixOf text then position
        else
          let rest := text.drop 1
          let rest := if blobs then rest else rest.dropWhile (· &&& 0xC0 == 0x80)
          search rest (position + 1) fuel
    let haystackBytes := haystack.textBytes
    .integer (if needleBytes.isEmpty then 1 else search haystackBytes 1 haystackBytes.length)

/-- {lit}`replace(x, pattern, replacement)` ({lit}`replaceFunc`): each occurrence of the pattern
in the bytes of {lit}`x`, from the left and without overlap, replaced. A NULL argument gives
NULL; a pattern that is empty or starts with NUL gives {lit}`x` as text. -/
def replaceValue (value pattern replacement : Value) : Value :=
  if value.isNull || pattern.isNull then .null
  else
    let patternBytes := pattern.textBytes
    if patternBytes.headD 0 == 0 then .text value.textBytes
    else if replacement.isNull then .null
    else
      let rec go : Nat → List UInt8 → List UInt8
        | 0, text => text
        | fuel + 1, text =>
          if text.isEmpty then []
          else if patternBytes.isPrefixOf text then replacement.textBytes ++ go fuel (text.drop patternBytes.length)
          else text.head! :: go fuel text.tail
      let bytes := value.textBytes
      .text (go bytes.length bytes)

/-- The UTF-8 characters of a C string, each as its bytes ({lit}`SQLITE_SKIP_UTF8`). -/
def utf8Characters (fuel : Nat) (bytes : List UInt8) : List (List UInt8) :=
  match fuel, bytes with
  | 0, _ | _, [] => []
  | fuel + 1, text =>
    let rest := utf8Skip text
    text.take (text.length - rest.length) :: utf8Characters fuel rest

/-- {lit}`trim(x [, characters])` and its sides ({lit}`trimFunc`): the bytes of {lit}`x` without
the characters of the set at the cut ends; the set is a space without a second argument, and
the characters of its C string with one. NULL gives NULL; an empty set cuts nothing. -/
def trimValue (side : TrimSide) (value : Value) (characters : Option Value) : Value :=
  if value.isNull || characters.any (·.isNull) then .null
  else
    let set := match characters with
      | none => [[32]]
      | some set => let bytes := bytesBeforeNul set.textBytes; utf8Characters bytes.length bytes
    let bytes := value.textBytes
    let rec front : Nat → List UInt8 → List UInt8
      | 0, text => text
      | fuel + 1, text => match set.find? fun character => character.isPrefixOf text with
        | some character => if text.isEmpty then text else front fuel (text.drop character.length)
        | none => text
    let rec back : Nat → List UInt8 → List UInt8
      | 0, text => text
      | fuel + 1, text => match set.find? fun character => character.reverse.isPrefixOf text.reverse with
        | some character => if text.isEmpty then text else back fuel (text.take (text.length - character.length))
        | none => text
    if set.isEmpty then .text bytes
    else
      let bytes := if side == .trailing then bytes else front bytes.length bytes
      .text (if side == .leading then bytes else back bytes.length bytes)

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

/-- {lit}`unhex(x [, ignored])` ({lit}`unhexFunc`): the BLOB of the hexadecimal digit pairs of the C
string {lit}`x`; a character of {lit}`ignored` between pairs is skipped. A NULL argument, an odd
digit, or another character gives NULL. -/
def unhexValue (value : Value) (ignored : Option Value) : Value :=
  if value.isNull || ignored.any (·.isNull) then .null
  else
    let skip := ((ignored.map fun pass => utf8Characters pass.textBytes.length pass.textBytes).getD []).map
      fun character => (utf8Read character).1
    let rec go : Nat → List UInt8 → Option (List UInt8)
      | 0, _ => some []
      | _, [] => some []
      | fuel + 1, text@(high :: rest) => match hexDigitValue high with
        | some upper => match rest with
          | low :: after => match hexDigitValue low with
            | some lower => (((upper <<< 4) ||| lower) :: ·) <$> go fuel after
            | none => none
          | [] => none
        | none =>
          let (character, after) := utf8Read text
          if skip.contains character then go fuel after else none
    let bytes := bytesBeforeNul value.textBytes
    match go bytes.length bytes with
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

/-- {lit}`unistr(x)` ({lit}`unistrFunc`): the text with its escapes replaced: {lit}`\\` by a backslash,
and {lit}`\XXXX`, {lit}`\uXXXX`, {lit}`\+XXXXXX` and {lit}`\UXXXXXXXX` by the UTF-8 bytes of the code
point. Escapes count only before the first NUL; the bytes after it stay. NULL gives NULL, and
any other backslash fails with {lit}`invalid Unicode escape` (none). -/
def unistrValue (value : Value) : Option Value :=
  if value.isNull then some .null
  else
    let rec go : Nat → List UInt8 → Option (List UInt8)
      | 0, text => some text
      | _, [] => some []
      | fuel + 1, byte :: rest =>
        if byte == 0 then some (byte :: rest)
        else if byte != 92 then (byte :: ·) <$> go fuel rest
        else match rest with
          | 92 :: after => (92 :: ·) <$> go fuel after
          | 43 :: after => (hexCode 6 after).bind fun code => (utf8Bytes code ++ ·) <$> go fuel (after.drop 6)
          | 117 :: after => (hexCode 4 after).bind fun code => (utf8Bytes code ++ ·) <$> go fuel (after.drop 4)
          | 85 :: after => (hexCode 8 after).bind fun code => (utf8Bytes code ++ ·) <$> go fuel (after.drop 8)
          | after => (hexCode 4 after).bind fun code => (utf8Bytes code ++ ·) <$> go fuel (after.drop 4)
    let bytes := value.textBytes
    (Value.text ·) <$> go bytes.length bytes

/-- {lit}`concat(x, ...)` and {lit}`concat_ws(separator, x, ...)` ({lit}`concatFuncCore`): the text of
all the bytes of the arguments that are not NULL, with the separator between two of them. -/
def concatValue (separator : List UInt8) (values : List Value) : Value :=
  .text (List.intercalate separator ((values.filter (!·.isNull)).map Value.textBytes))

end Belay.Sqlite.Resolved
