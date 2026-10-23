import Belay.Sqlite.Model.ByteText
set_option doc.verso true

/-! Byte classes of the SQLite 3.51.0 JSON reader ({lit}`jsonIsSpace`, {lit}`jsonIsOk`,
{lit}`sqlite3CtypeMap`) and its JSON5 white space ({lit}`json5Whitespace`). SQLite reads
the JSON text as a NUL-terminated C string, so the model reads byte 0 past the end. -/

namespace Belay.Sqlite.Model.Json

/-- The byte at an index of a text, or 0 past the end. SQLite reads a NUL-terminated
buffer, so a read past the last byte gives the terminator. -/
def byteAt (text : Array UInt8) (index : Nat) : UInt8 := text.getD index 0

/-- Whether a byte is JSON white space for SQLite ({lit}`jsonIsspace`): tab, line feed,
carriage return or space. Vertical tab and form feed are JSON5 white space only. -/
def isJsonSpace (byte : UInt8) : Bool := byte == 9 || byte == 10 || byte == 13 || byte == 32

/-- Whether a string byte needs no special handling ({lit}`jsonIsOk`): every byte except
control bytes, the double quote, the single quote and the backslash. -/
def isJsonOk (byte : UInt8) : Bool := byte ≥ 0x20 && byte != 0x22 && byte != 0x27 && byte != 0x5c

/-- Whether a byte is an ASCII digit ({lit}`sqlite3Isdigit`). -/
def isAsciiDigit (byte : UInt8) : Bool := 48 ≤ byte && byte ≤ 57

/-- Whether a byte is an ASCII letter ({lit}`sqlite3Isalpha`). -/
def isAsciiAlpha (byte : UInt8) : Bool := (65 ≤ byte && byte ≤ 90) || (97 ≤ byte && byte ≤ 122)

/-- Whether a byte is an ASCII letter or digit ({lit}`sqlite3Isalnum`). -/
def isAsciiAlnum (byte : UInt8) : Bool := isAsciiDigit byte || isAsciiAlpha byte

/-- Whether a byte is an ASCII hexadecimal digit ({lit}`sqlite3Isxdigit`). -/
def isHexDigit (byte : UInt8) : Bool :=
  isAsciiDigit byte || (65 ≤ byte && byte ≤ 70) || (97 ≤ byte && byte ≤ 102)

/-- Whether a byte can start an unquoted JSON5 object label ({lit}`sqlite3JsonId1`): a
letter, {lit}`$`, {lit}`_` or a byte of a non-ASCII character. -/
def isLabelStart (byte : UInt8) : Bool := isAsciiAlpha byte || byte == 36 || byte == 95 || byte ≥ 0x80

/-- Whether a byte can continue an unquoted JSON5 object label ({lit}`sqlite3JsonId2`):
a label start byte or a digit. -/
def isLabelPart (byte : UInt8) : Bool := isLabelStart byte || isAsciiDigit byte

/-- The value of a hexadecimal digit ({lit}`jsonHexToInt`). The arithmetic is SQLite's:
it gives a value in 0 to 15 for every byte, also for a byte that is not a digit. -/
def hexValue (byte : UInt8) : UInt32 :=
  let h := byte.toUInt32
  (h + (9 : UInt32) * ((h >>> 6) &&& 1)) &&& 0xf

/-- Whether the text has a hexadecimal digit at each of {lit}`count` positions from
{lit}`start` ({lit}`jsonIs2Hex`, {lit}`jsonIs4Hex`). -/
def hasHexDigits (text : Array UInt8) (start count : Nat) : Bool :=
  (List.range count).all fun offset => isHexDigit (byteAt text (start + offset))

/-- Whether the first {lit}`count` bytes of a list are hexadecimal digits, with byte 0 after
the end as in {name}`byteAt`: the check of {name}`hasHexDigits` for a reader that walks the
bytes after its position. -/
def hexDigitsAhead (bytes : List UInt8) (count : Nat) : Bool :=
  (List.range count).all fun offset => isHexDigit (bytes.getD offset 0)

/-- The bytes of the text from {lit}`start` up to, not including, {lit}`stop`, with byte 0
for each position past the end, as in {name}`byteAt`. The bytes come from one walk over
the list: a kernel proof that reads each byte by its index ({name}`byteAt`) does work in
proportion to the index, so a slice by indices is quadratic in its length. -/
def slice (text : Array UInt8) (start stop : Nat) : List UInt8 :=
  ((text.toList.drop start) ++ List.replicate (stop - start) 0).take (stop - start)

/-- For every text, position and offset, byte {lit}`offset` of the list of the text from
{lit}`position` on, with byte 0 past its end, is {name}`byteAt` of the text at
{lit}`position + offset`. Proof sketch: both sides become optional indexing, and indexing
into {lit}`List.drop` adds the dropped count to the index. -/
theorem drop_getD_eq_byteAt (text : Array UInt8) (position offset : Nat) :
    (text.toList.drop position).getD offset 0 = byteAt text (position + offset) := by
  simp [byteAt, List.getD_eq_getElem?_getD, List.getElem?_drop, Array.getD_eq_getD_getElem?]

/-- For every text and positions {lit}`start` and {lit}`stop`, {name}`slice` gives, for each
offset below {lit}`stop - start`, the byte {name}`byteAt` at {lit}`start` plus the offset. A
start at or after the stop gives the empty list. Proof sketch: compare the lists index by
index; an index inside the text reads it with {name}`drop_getD_eq_byteAt`, and an index past
its end reads the padding 0, as {name}`byteAt` does. -/
theorem slice_eq_map_byteAt (text : Array UInt8) (start stop : Nat) :
    slice text start stop = (List.range (stop - start)).map fun offset => byteAt text (start + offset) := by
  apply List.ext_getElem?
  intro index
  simp only [slice, List.getElem?_take, List.getElem?_map]
  by_cases inside : index < stop - start
  · rw [List.getElem?_range inside]
    simp only [inside, ite_true, Option.map_some]
    rw [← drop_getD_eq_byteAt text start index, List.getD_eq_getElem?_getD, List.getElem?_append]
    split
    · next inText => simp [List.getElem?_eq_getElem inText]
    · next pastText =>
      have : (List.drop start text.toList)[index]? = none := List.getElem?_eq_none (by omega)
      simp only [this, Option.getD_none, List.getElem?_replicate]
      split <;> first | rfl | omega
  · simp [inside]

/-- The first position at or after {lit}`position` that is not a hexadecimal digit. -/
def hexDigitsEnd (text : Array UInt8) : Nat → Nat → Nat
  | 0, position => position
  | fuel + 1, position =>
    if isHexDigit (byteAt text position) then hexDigitsEnd text fuel (position + 1) else position

/-- Whether the text at {lit}`start` begins with the ASCII pattern, with the case of
letters ignored ({lit}`sqlite3StrNICmp`). A NUL byte in the text never matches. -/
def matchesIgnoringCase (text : Array UInt8) (start : Nat) (pattern : List UInt8) : Bool :=
  (List.range pattern.length).all fun offset =>
    lowerAscii (byteAt text (start + offset)) == lowerAscii (pattern.getD offset 0)

/-- Whether the text at {lit}`start` begins with exactly the pattern bytes
({lit}`strncmp`). -/
def matchesExactly (text : Array UInt8) (start : Nat) (pattern : List UInt8) : Bool :=
  (List.range pattern.length).all fun offset => byteAt text (start + offset) == pattern.getD offset 0

/-- The position after the {lit}`*/` that closes a block comment, searched from
{lit}`position`; {lit}`none` when the text ends first. A {lit}`/` closes the comment when
the byte before it is a {lit}`*`. -/
def blockCommentEnd (text : Array UInt8) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, position =>
    let byte := byteAt text position
    if byte == 47 && byteAt text (position - 1) == 42 then some (position + 1)
    else if byte == 0 then none
    else blockCommentEnd text fuel (position + 1)

/-- The position after a line comment, searched from {lit}`position`: after the line
feed, the carriage return or the U+2028 or U+2029 separator that ends it, or at the end
of the text. -/
def lineCommentEnd (text : Array UInt8) : Nat → Nat → Nat
  | 0, position => position
  | fuel + 1, position =>
    let byte := byteAt text position
    if byte == 0 then position
    else if byte == 10 || byte == 13 then position + 1
    else if byte == 0xe2 && byteAt text (position + 1) == 0x80
        && (byteAt text (position + 2) == 0xa8 || byteAt text (position + 2) == 0xa9) then position + 3
    else lineCommentEnd text fuel (position + 1)

/-- The length of the multi-byte JSON5 space character at a position, or 0: U+00A0,
U+1680, U+2000 to U+200A, U+2028, U+2029, U+202F, U+205F, U+3000 and U+FEFF. -/
def unicodeSpaceLength (text : Array UInt8) (position : Nat) : Nat :=
  let b0 := byteAt text position
  let b1 := byteAt text (position + 1)
  let b2 := byteAt text (position + 2)
  if b0 == 0xc2 then (if b1 == 0xa0 then 2 else 0)
  else if b0 == 0xe1 then (if b1 == 0x9a && b2 == 0x80 then 3 else 0)
  else if b0 == 0xe2 then
    if b1 == 0x80 then (if b2 ≥ 0x80 && (b2 ≤ 0x8a || b2 == 0xa8 || b2 == 0xa9 || b2 == 0xaf) then 3 else 0)
    else if b1 == 0x81 && b2 == 0x9f then 3 else 0
  else if b0 == 0xe3 then (if b1 == 0x80 && b2 == 0x80 then 3 else 0)
  else if b0 == 0xef then (if b1 == 0xbb && b2 == 0xbf then 3 else 0)
  else 0

/-- Skip JSON5 white space from a position ({lit}`json5Whitespace`): ASCII spaces,
vertical tab, form feed, the Unicode spaces of {name}`unicodeSpaceLength`, block comments
that close and line comments. The result is the first position that is not white
space; an unclosed block comment stops the skip at its {lit}`/`. -/
def json5SpaceEndFrom (text : Array UInt8) : Nat → Nat → Nat
  | 0, position => position
  | fuel + 1, position =>
    let byte := byteAt text position
    if byte == 32 || (9 ≤ byte && byte ≤ 13) then json5SpaceEndFrom text fuel (position + 1)
    else if byte == 47 then
      let next := byteAt text (position + 1)
      if next == 42 && byteAt text (position + 2) != 0 then
        match blockCommentEnd text (text.size + 1) (position + 3) with
        | some after => json5SpaceEndFrom text fuel after
        | none => position
      else if next == 47 then json5SpaceEndFrom text fuel (lineCommentEnd text (text.size + 1) (position + 2))
      else position
    else
      let length := unicodeSpaceLength text position
      if length > 0 then json5SpaceEndFrom text fuel (position + length) else position

/-- The first position at or after {lit}`position` that is not JSON5 white space. -/
def json5SpaceEnd (text : Array UInt8) (position : Nat) : Nat :=
  json5SpaceEndFrom text (text.size + 1) position

end Belay.Sqlite.Model.Json
