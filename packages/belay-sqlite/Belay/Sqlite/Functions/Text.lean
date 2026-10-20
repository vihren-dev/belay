import Belay.Sqlite.Arithmetic
import Belay.Sqlite.ByteText
import Belay.Sqlite.Functions.Utf8
import Belay.Sqlite.Resolution.ScalarFunction

set_option doc.verso true

/-! The text functions of ADR 0015, slice 1, ported from SQLite 3.51.0's {lit}`func.c` over byte
lists: {lit}`lower`, {lit}`upper`, {lit}`substr`, {lit}`instr`, {lit}`replace`, the {lit}`trim`
family, {lit}`concat` and {lit}`concat_ws`; {lit}`Codes.lean` has the functions of bytes and
code points. Each function reads its arguments as SQLite's C functions do: some read all
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

/-- SQLite's length limit ({lit}`SQLITE_LIMIT_LENGTH`, 1000000000 by default): the count of
{lit}`substr` without a count argument. -/
def lengthLimit : Int := 1000000000

/-- {lit}`substr(x, start [, count])` ({lit}`substrFunc`): characters of text before its first NUL,
or bytes of a BLOB. A positive start counts from 1, a negative one from the end, and a zero
start takes one character less; a negative count takes the characters before the start. A
NULL value, a NULL count, a NULL start of 0, and an empty BLOB, which SQLite reads as no pointer, give
NULL. Without a count, the count is
{name}`lengthLimit`. -/
def substrValue (value start : Value) (count : Option Value) : Value :=
  if value.isNull || value == .blob [] then .null
  else if count.any (·.isNull) then .null
  else if start.isNull then .null
  else
    let blob := value matches .blob _
    let bytes := if blob then value.textBytes else bytesBeforeNul value.textBytes
    let p1 := start.toInt64
    let p2 := (count.map Value.toInt64).getD lengthLimit
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

/-- The position of the needle in the text from {lit}`position` on, as {lit}`instrFunc` searches:
one step per character of text ({lit}`characters`) or per byte, 0 when the needle is longer
than the rest. The fuel bounds the steps. -/
def instrSearch (needle : List UInt8) (characters : Bool) : List UInt8 → Nat → Nat → Nat
  | text, position, 0 => if needle.isPrefixOf text then position else 0
  | text, position, fuel + 1 =>
    if needle.length > text.length then 0
    else if needle.isPrefixOf text then position
    else
      let rest := text.drop 1
      instrSearch needle characters (if characters then rest.dropWhile (· &&& 0xC0 == 0x80) else rest)
        (position + 1) fuel

/-- The 1-based position of the first occurrence of the needle ({lit}`instrFunc`), counted in
characters for text and in bytes when both are BLOBs, 1 for an empty needle, 0 when it does not
occur, and NULL when an argument is NULL. Text compares all the bytes of the values; a BLOB
and a text compare as text. The fuel is the length of the haystack. -/
def instrValue (haystack needle : Value) : Value :=
  if haystack.isNull || needle.isNull then .null
  else
    let blobs := (haystack matches .blob _) && (needle matches .blob _)
    let needleBytes := needle.textBytes
    let haystackBytes := haystack.textBytes
    .integer (if needleBytes.isEmpty then 1 else instrSearch needleBytes (!blobs) haystackBytes 1 haystackBytes.length)

/-- The bytes with each occurrence of the pattern, from the left and without overlap, replaced.
The fuel bounds the steps; the length of the bytes is enough. -/
def replaceAll (pattern replacement : List UInt8) : Nat → List UInt8 → List UInt8
  | 0, text => text
  | fuel + 1, text =>
    match text with
    | [] => []
    | byte :: rest =>
      if pattern.isPrefixOf text then replacement ++ replaceAll pattern replacement fuel (text.drop pattern.length)
      else byte :: replaceAll pattern replacement fuel rest

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
      let bytes := value.textBytes
      .text (replaceAll patternBytes replacement.textBytes bytes.length bytes)

/-- The UTF-8 characters of a C string, each as its bytes ({lit}`SQLITE_SKIP_UTF8`). -/
def utf8Characters (fuel : Nat) (bytes : List UInt8) : List (List UInt8) :=
  match fuel, bytes with
  | 0, _ | _, [] => []
  | fuel + 1, text =>
    let rest := utf8Skip text
    text.take (text.length - rest.length) :: utf8Characters fuel rest

/-- The bytes without the characters of the set at the start, as {lit}`trimFunc` cuts them: the
first character of the set that starts the bytes, again until none does. The fuel bounds the
cuts. -/
def trimFront (set : List (List UInt8)) : Nat → List UInt8 → List UInt8
  | 0, text => text
  | fuel + 1, text => match set.find? fun character => !character.isEmpty && character.isPrefixOf text with
    | some character => trimFront set fuel (text.drop character.length)
    | none => text

/-- The bytes without the characters of the set at the end, as {name}`trimFront` cuts the start. -/
def trimBack (set : List (List UInt8)) : Nat → List UInt8 → List UInt8
  | 0, text => text
  | fuel + 1, text =>
    match set.find? fun character => !character.isEmpty && character.reverse.isPrefixOf text.reverse with
    | some character => trimBack set fuel (text.take (text.length - character.length))
    | none => text

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
    if set.isEmpty then .text bytes
    else
      let bytes := if side == .trailing then bytes else trimFront set bytes.length bytes
      .text (if side == .leading then bytes else trimBack set bytes.length bytes)

/-- {lit}`concat(x, ...)` and {lit}`concat_ws(separator, x, ...)` ({lit}`concatFuncCore`): the text of
all the bytes of the arguments that are not NULL, with the separator between two of them. -/
def concatValue (separator : List UInt8) (values : List Value) : Value :=
  .text (List.intercalate separator ((values.filter (!·.isNull)).map Value.textBytes))

end Belay.Sqlite.Resolved
