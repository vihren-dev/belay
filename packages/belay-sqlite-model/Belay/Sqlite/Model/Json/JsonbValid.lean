import Belay.Sqlite.Model.Json.JsonbOffset
import Belay.Sqlite.Model.Json.Bytes
import Belay.Sqlite.Model.Json.Unescape
import Belay.Sqlite.Model.Json.Read

set_option doc.verso true

/-! The checks of a JSONB BLOB (ADR 0015, slice 4), from SQLite 3.51.0's {lit}`json.c`: the
reader of a header ({lit}`jsonbPayloadSize`), the full check ({lit}`jsonbValidityCheck`) and
the quick check of a BLOB argument ({lit}`jsonArgIsJsonb`). -/

namespace Belay.Sqlite.Model.Json

/-- The header length and the payload size of the node at {lit}`index` ({lit}`jsonbPayloadSize`
with no pending edit): none when the header does not fit in the BLOB, when an 8-byte size
has a high half that is not zero, or when the payload goes past the end. -/
def jsonbHeaderAt (blob : Array UInt8) (index : Nat) : Option (Nat × Nat) :=
  let length := blob.size
  let byte := fun offset => (byteAt blob (index + offset)).toNat
  let kind := byte 0 / 16
  let header : Option (Nat × Nat) :=
    if kind ≤ 11 then some (1, kind)
    else if kind == 12 then (if index + 1 ≥ length then none else some (2, byte 1))
    else if kind == 13 then (if index + 2 ≥ length then none else some (3, byte 1 * 0x100 + byte 2))
    else if kind == 14 then
      (if index + 4 ≥ length then none else some (5, ((byte 1 * 0x100 + byte 2) * 0x100 + byte 3) * 0x100 + byte 4))
    else if index + 8 ≥ length || byte 1 != 0 || byte 2 != 0 || byte 3 != 0 || byte 4 != 0 then none
    else some (9, ((byte 5 * 0x100 + byte 6) * 0x100 + byte 7) * 0x100 + byte 8)
  header.bind fun (headerLength, size) => if index + size + headerLength > length then none else some (headerLength, size)

/-- Whether the bytes from {lit}`position` to {lit}`stop` are hex digits ({lit}`hex`) or
decimal digits. -/
def jsonbDigitsUpTo (blob : Array UInt8) (hex : Bool) : Nat → Nat → Nat → Bool
  | 0, _, _ => Bool.true
  | fuel + 1, position, stop =>
    if position ≥ stop then Bool.true
    else if (if hex then isHexDigit else isAsciiDigit) (byteAt blob position) then jsonbDigitsUpTo blob hex fuel (position + 1) stop
    else Bool.false

/-- The rest of the check of a {lit}`JSONB_FLOAT` or {lit}`JSONB_FLOAT5` payload from
{lit}`position` to {lit}`stop` ({lit}`jsonbValidityCheck`): digits, one point (in
{lit}`JSONB_FLOAT` followed by a digit), one exponent with an optional sign and not at the end;
{lit}`seen` is 0 at first, 1 after a point and 2 after an exponent, and the payload needs a
point or an exponent. -/
def jsonbFloatRestValid (blob : Array UInt8) (five : Bool) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, seen => seen != 0
  | fuel + 1, position, stop, seen =>
    if position ≥ stop then seen != 0
    else
      let byte := byteAt blob position
      if isAsciiDigit byte then jsonbFloatRestValid blob five fuel (position + 1) stop seen
      else if byte == 46 then
        if seen > 0 then Bool.false
        else if !five && (position + 1 == stop || !isAsciiDigit (byteAt blob (position + 1))) then Bool.false
        else jsonbFloatRestValid blob five fuel (position + 1) stop 1
      else if byte == 101 || byte == 69 then
        if seen == 2 || position + 1 == stop then Bool.false
        else
          let signed := byteAt blob (position + 1) == 43 || byteAt blob (position + 1) == 45
          if signed && position + 2 == stop then Bool.false
          else jsonbFloatRestValid blob five fuel (position + (if signed then 2 else 1)) stop 2
      else Bool.false

/-- The check of a number payload from {lit}`start` with {lit}`size` bytes
({lit}`jsonbValidityCheck` for {lit}`JSONB_INT`, {lit}`JSONB_INT5`, {lit}`JSONB_FLOAT` and
{lit}`JSONB_FLOAT5`). -/
def jsonbNumberValid (blob : Array UInt8) (code : UInt8) (start size : Nat) : Bool :=
  let stop := start + size
  let negative := byteAt blob start == 45
  let first := if negative then start + 1 else start
  if code == 3 then size ≥ 1 && (!negative || size ≥ 2) && jsonbDigitsUpTo blob Bool.false size first stop
  else if code == 4 then
    size ≥ 3 && (!negative || size ≥ 4) && byteAt blob first == 48 &&
      (byteAt blob (first + 1) == 120 || byteAt blob (first + 1) == 88) && jsonbDigitsUpTo blob Bool.true size (first + 2) stop
  else
    let five := code == 6
    if size < 2 || (negative && size < 3) then Bool.false
    else if byteAt blob first == 46 then
      five && isAsciiDigit (byteAt blob (first + 1)) && jsonbFloatRestValid blob five size (first + 2) stop 1
    else if byteAt blob first == 48 && !five then
      first + 3 ≤ stop && [46, 101, 69].contains (byteAt blob (first + 1)) &&
        jsonbFloatRestValid blob five size (first + 1) stop 0
    else jsonbFloatRestValid blob five size first stop 0

/-- The check of a string payload from {lit}`position` to {lit}`stop` ({lit}`jsonbValidityCheck`
for {lit}`JSONB_TEXT`, {lit}`JSONB_TEXTJ` and {lit}`JSONB_TEXT5`): {lit}`TEXT` allows no
escapes, {lit}`TEXTJ` the JSON escapes, and {lit}`TEXT5` also a double quote, control bytes and
the JSON5 escapes. -/
def jsonbTextValid (blob : Array UInt8) (code : UInt8) : Nat → Nat → Nat → Bool
  | 0, _, _ => Bool.true
  | fuel + 1, position, stop =>
    if position ≥ stop then Bool.true
    else
      let byte := byteAt blob position
      let next := byteAt blob (position + 1)
      if isJsonOk byte || byte == 39 then jsonbTextValid blob code fuel (position + 1) stop
      else if code == 7 then Bool.false
      else if byte == 34 || byte ≤ 0x1f then code == 9 && jsonbTextValid blob code fuel (position + 1) stop
      else if byte != 92 || position + 1 ≥ stop then Bool.false
      else if [34, 92, 47, 98, 102, 110, 114, 116, 0].contains next then jsonbTextValid blob code fuel (position + 2) stop
      else if next == 117 then
        position + 5 < stop && hasHexDigits blob (position + 2) 4 && jsonbTextValid blob code fuel (position + 2) stop
      else if code != 9 then Bool.false
      else
        let (char, used) := unescapeOneChar (stop - position) ((blob.extract position stop).toList)
        char != invalidChar && jsonbTextValid blob code fuel (position + used) stop

mutual
/-- Whether the node from {lit}`index` to {lit}`stop` is valid JSONB at a nesting depth
({lit}`jsonbValidityCheck`): its header fills the range; a literal has no payload; a number or
string payload passes its check; the children of an array are valid and fill it; the children
of an object are labels (a string type) and values in pairs. The depth is at most
{name}`maxDepth`, as for JSON text. -/
def jsonbValid (blob : Array UInt8) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => Bool.false
  | fuel + 1, index, stop, depth =>
    match jsonbHeaderAt blob index with
    | none => Bool.false
    | some (headerLength, size) =>
      let code := byteAt blob index % 16
      let start := index + headerLength
      if depth > maxDepth || start + size != stop then Bool.false
      else if code ≤ 2 then headerLength + size == 1
      else if code ≤ 6 then jsonbNumberValid blob code start size
      else if code ≤ 9 then jsonbTextValid blob code size start stop
      else if code == 10 then Bool.true
      else if code == 11 then childrenValid blob fuel start stop (depth + 1) none
      else if code == 12 then childrenValid blob fuel start stop (depth + 1) (some 0)
      else Bool.false

/-- Whether the children from {lit}`index` to {lit}`stop` are valid nodes that fill the range;
for an object, {lit}`count` is the number of children so far, an even one must be a label,
and the count must end even. -/
def childrenValid (blob : Array UInt8) : Nat → Nat → Nat → Nat → Option Nat → Bool
  | 0, _, _, _, _ => Bool.false
  | fuel + 1, index, stop, depth, count =>
    if index ≥ stop then count.all (· % 2 == 0)
    else match jsonbHeaderAt blob index with
      | none => Bool.false
      | some (headerLength, size) =>
        let next := index + headerLength + size
        let code := byteAt blob index % 16
        next ≤ stop && (count.all fun count => count % 2 == 1 || (7 ≤ code && code ≤ 10)) &&
          jsonbValid blob fuel index next depth && childrenValid blob fuel next stop depth (count.map (· + 1))
end

/-- The fuel of a walk over a BLOB: every call of the walk reads a header byte of its own or
moves past one, so twice the size and two more is enough. -/
def jsonbFuel (blob : Array UInt8) : Nat := 2 * blob.size + 2

/-- Whether a BLOB is JSONB by SQLite's quick check of an argument ({lit}`jsonArgIsJsonb`): it is
not empty, its first node type is one of the 13 types, its header gives a payload that ends the
BLOB, a literal has no payload, and a payload of at most 7 bytes whose first byte is
{lit}`{`, {lit}`[` or a digit passes the full check. -/
def isJsonb (bytes : List UInt8) : Bool :=
  let blob := bytes.toArray
  let first := byteAt blob 0
  match jsonbHeaderAt blob 0 with
  | none => Bool.false
  | some (headerLength, size) =>
    !bytes.isEmpty && first % 16 ≤ 12 && size + headerLength == blob.size && (first % 16 > 2 || size == 0) &&
      (size > 7 || (first != 0x7b && first != 0x5b && !isAsciiDigit first) ||
        jsonbValid blob (jsonbFuel blob) 0 blob.size 1)

end Belay.Sqlite.Model.Json
