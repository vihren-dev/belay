import Belay.Sqlite.Json.Unescape
import Belay.Sqlite.Json.ReadScalar
import Belay.Sqlite.Json.JsonbOffset

set_option doc.verso true

/-! SQLite's JSON path lookup ({lit}`jsonLookupStep` in 3.51.0) without edits, the one
walker of {lit}`json_extract`, the arrow operators and {lit}`json_each`. It keeps the JSONB
offsets of the node it finds, which {lit}`json_each` reports. The path
is the text after the {lit}`$`: steps {lit}`.label`, {lit}`."label"`, {lit}`[N]`,
{lit}`[#]` and {lit}`[#-N]`. The lookup checks a step only when it reaches it, so a step
that does not fit the node gives "not found" before the rest of the path is checked. -/

namespace Belay.Sqlite.Json

/-- The result of a path lookup. -/
inductive LookupResult where
  /-- The node that the path selects, with its JSONB offsets. -/
  | found (located : LocatedNode)
  /-- No node at the path ({lit}`JSON_LOOKUP_NOTFOUND`). -/
  | notFound
  /-- The path has bad syntax ({lit}`JSON_LOOKUP_PATHERROR`). -/
  | pathError
  /-- The JSON is malformed ({lit}`JSON_LOOKUP_ERROR`); a parsed text never gives it. -/
  | malformed

/-- The position of the closing quote of a quoted label that starts after the quote at
{lit}`position`, or of the NUL byte that ends the path. A backslash skips the next byte. -/
def quotedLabelEnd (path : Array UInt8) : Nat → Nat → Nat
  | 0, position => position
  | fuel + 1, position =>
    let byte := byteAt path position
    if byte == 0 || byte == 34 then position
    else if byte == 92 && byteAt path (position + 1) != 0 then quotedLabelEnd path fuel (position + 2)
    else quotedLabelEnd path fuel (position + 1)

/-- The position of the {lit}`.`, {lit}`[` or NUL byte that ends an unquoted label. -/
def plainLabelEnd (path : Array UInt8) : Nat → Nat → Nat
  | 0, position => position
  | fuel + 1, position =>
    let byte := byteAt path position
    if byte == 0 || byte == 46 || byte == 91 then position else plainLabelEnd path fuel (position + 1)

/-- Read decimal digits into a 32-bit value that wraps as C's {lit}`u32` does: the value
and the position after the digits. -/
def readIndexDigits (path : Array UInt8) : Nat → Nat → UInt32 → UInt32 × Nat
  | 0, position, value => (value, position)
  | fuel + 1, position, value =>
    let byte := byteAt path position
    if isAsciiDigit byte then readIndexDigits path fuel (position + 1) (value * 10 + (byte - 48).toUInt32)
    else (value, position)

/-- The label of a {lit}`.` step after the dot at {lit}`position`: the key bytes, whether
they have no escapes, and the position after the label; {lit}`none` for an unclosed
quote or an empty unquoted label. -/
def readPathLabel (path : Array UInt8) (position : Nat) : Option (List UInt8 × Bool × Nat) :=
  let fuel := path.size + 1
  if byteAt path position == 34 then
    let close := quotedLabelEnd path fuel (position + 1)
    if byteAt path close == 0 then none
    else
      let key := slice path (position + 1) close
      some (key, !key.contains 92, close + 1)
  else
    let stop := plainLabelEnd path fuel position
    if stop == position then none else some (slice path position stop, Bool.true, stop)

/-- The array index of a {lit}`[` step at {lit}`position` for an array of {lit}`count`
elements: the index and the position of the closing {lit}`]`. {lit}`[#]` is the count
and {lit}`[#-N]` the count minus N. The outer {lit}`none` is a path error; the inner
{lit}`none` is an index before the first element. -/
def readPathIndex (path : Array UInt8) (position count : Nat) : Option (Option (UInt32 × Nat)) :=
  let fuel := path.size + 1
  let (index, stop) := readIndexDigits path fuel (position + 1) 0
  if stop ≥ position + 2 && byteAt path stop == 93 then some (some (index, stop))
  else if byteAt path (position + 1) == 35 then
    let total := UInt32.ofNat count
    if byteAt path (position + 2) == 45 && isAsciiDigit (byteAt path (position + 3)) then
      let (back, stop) := readIndexDigits path fuel (position + 3) 0
      if back > total then some none
      else if byteAt path stop == 93 then some (some (total - back, stop)) else none
    else if byteAt path (position + 2) == 93 then some (some (total, position + 2)) else none
  else none

/-- The first member whose label equals the key, with the offsets of its label and its
value when the members start at {lit}`offset`: {lit}`none` when no label matches, and
{lit}`some none` for a label that is not a string. -/
def findMember (key : List UInt8) (rawKey : Bool) :
    List (JsonNode × JsonNode) → Nat → Option (Option (Nat × Nat × JsonNode))
  | [], _ => none
  | (label, value) :: rest, offset =>
    match label.labelText with
    | none => some none
    | some (text, rawLabel) =>
      if labelsMatch key rawKey text rawLabel then some (some (offset, offset + jsonbSize label, value))
      else findMember key rawKey rest (offset + jsonbSize label + jsonbSize value)

/-- Follow the path from {lit}`position` in a located node ({lit}`jsonLookupStep`), and
keep the JSONB offsets. The path ends at its first NUL byte. A label step on a node that
is not an object, or an index step on a node that is not an array, gives
{lit}`notFound`. -/
def lookupStep (path : Array UInt8) : Nat → Nat → LocatedNode → LookupResult
  | 0, _, _ => .pathError
  | fuel + 1, position, located =>
    let byte := byteAt path position
    if byte == 0 then .found located
    else if byte == 46 then
      match readPathLabel path (position + 1) with
      | none => .pathError
      | some (key, rawKey, next) =>
        match located.node with
        | .object members =>
          match findMember key rawKey members (jsonbChildrenStart located.node located.offset) with
          | none => .notFound
          | some none => .malformed
          | some (some (labelOffset, valueOffset, value)) =>
            lookupStep path fuel next ⟨value, valueOffset, some labelOffset⟩
        | .null | .true | .false | .int _ | .int5 _ | .float _ | .float5 _ | .text _ | .textj _ | .text5 _
        | .textraw _ | .array _ => .notFound
    else if byte == 91 then
      match located.node with
      | .array items =>
        match readPathIndex path position items.length with
        | none => .pathError
        | some none => .notFound
        | some (some (index, close)) =>
          match items[index.toNat]? with
          | some item =>
            let offset := jsonbItemOffset items index.toNat (jsonbChildrenStart located.node located.offset)
            lookupStep path fuel (close + 1) ⟨item, offset, none⟩
          | none => .notFound
      | .null | .true | .false | .int _ | .int5 _ | .float _ | .float5 _ | .text _ | .textj _ | .text5 _
      | .textraw _ | .object _ => .notFound
    else .pathError

/-- Look up a path text from a position in a whole document, whose root is at JSONB
offset 0: {lit}`lookupStep` with fuel for every step. -/
def lookupPath (path : List UInt8) (position : Nat) (root : JsonNode) : LookupResult :=
  lookupStep path.toArray (path.length + 2) position ⟨root, 0, none⟩

end Belay.Sqlite.Json
