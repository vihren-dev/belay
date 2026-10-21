import Lean.Data.Json

set_option doc.verso true

/-! Statement syntax as the model's JSON transport, with the source range of each node (ADR 0017,
S1, prototype 2, candidate A). The port of {lit}`belay/sqlite/located.py`: a model restriction
names a statement index and a node path, and each path step is the position of a constructor
argument or a structure field, then the index in a list, so the tree keeps that shape. -/

namespace Belay.Sqlite.Translation

open Lean (Json)

/-- One syntax value as JSON, its half-open UTF-8 byte range in the SQL text, and its located
parts in path order. For example, the name {lit}`t` at bytes 14 to 15 is
{lit}`{ value := "t", start := 14, stop := 15 }`. -/
structure Located where
  /-- The value in the model's JSON transport. -/
  value : Json
  /-- The first byte of the range. -/
  start : Nat
  /-- The byte after the range. -/
  stop : Nat
  /-- The located parts: constructor arguments or fields in order, or list items. -/
  children : Array Located := #[]
  deriving Inhabited

/-- A value without located parts, such as a name or a flag. -/
def leaf (value : Json) (start stop : Nat) : Located := { value, start, stop }

/-- A list value whose path steps are the item indexes. -/
def sequence (items : Array Located) (start stop : Nat) : Located :=
  { value := .arr (items.map (·.value)), start, stop, children := items }

/-- An object of the fields in order, and the fields as located parts. -/
def fieldObject (fields : Array (String × Located)) : Json :=
  Json.mkObj (fields.toList.map fun (field, part) => (field, part.value))

/-- A constructor with named arguments, encoded as Lean derives it: {lit}`{name: {field: value}}`. -/
def constructor (name : String) (fields : Array (String × Located)) (start stop : Nat) : Located :=
  { value := Json.mkObj [(name, fieldObject fields)], start, stop, children := fields.map (·.2) }

/-- A structure value, encoded as an object of its fields in declaration order. -/
def structure' (fields : Array (String × Located)) (start stop : Nat) : Located :=
  { value := fieldObject fields, start, stop, children := fields.map (·.2) }

/-- A Lean pair, encoded as a two-element array. -/
def pair (first second : Located) (start stop : Nat) : Located :=
  { value := .arr #[first.value, second.value], start, stop, children := #[first, second] }

/-- The located value as the JSON that {lit}`experiments/surface-s1/texts.py` writes for the
Python translation: its value, range and located parts. -/
partial def Located.toJson (item : Located) : Json :=
  Json.mkObj [("value", item.value), ("start", item.start), ("end", item.stop),
    ("children", .arr (item.children.map Located.toJson))]

/-- A string, or null for none. -/
def optionalText : Option String → Json
  | some text => .str text
  | none => .null

/-- A list of byte values as JSON numbers. -/
def byteList (bytes : ByteArray) : Json := .arr (bytes.toList.toArray.map fun byte => (byte.toNat : Json))

end Belay.Sqlite.Translation
