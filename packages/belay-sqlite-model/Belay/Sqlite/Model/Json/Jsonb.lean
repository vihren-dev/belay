import Belay.Sqlite.Model.Json.JsonbValid

set_option doc.verso true

/-! SQLite's binary JSON format, JSONB (ADR 0015, slice 4), from SQLite 3.51.0's
{lit}`json.c`: the encoder of a node tree ({lit}`jsonBlobAppendNode` with the smallest header,
as {lit}`jsonBlobChangePayloadSize` leaves a container) and the decoder of valid JSONB into the
node tree; the checks of a BLOB are in {lit}`Json.JsonbValid`. A node
of {lit}`JsonNode` has the JSONB node type of its constructor and keeps its payload, so the
encoding of a tree is determined by the tree. -/

namespace Belay.Sqlite.Model.Json

/-- The JSONB node type of a node ({lit}`JSONB_NULL` 0 to {lit}`JSONB_OBJECT` 12). -/
def JsonNode.typeCode : JsonNode → UInt8
  | .null => 0
  | .true => 1
  | .false => 2
  | .int _ => 3
  | .int5 _ => 4
  | .float _ => 5
  | .float5 _ => 6
  | .text _ => 7
  | .textj _ => 8
  | .text5 _ => 9
  | .textraw _ => 10
  | .array _ => 11
  | .object _ => 12

/-- The header of a node of a type with a payload of {lit}`size` bytes, as
{lit}`jsonBlobAppendNode` writes it: the size in the high four bits up to 11, else 12, 13 or
14 there and the size in 1, 2 or 4 bytes after it, most significant byte first. -/
def jsonbHeader (code : UInt8) (size : Nat) : List UInt8 :=
  if size ≤ 11 then [code + (size * 16).toUInt8]
  else if size ≤ 0xff then [code + 0xc0, size.toUInt8]
  else if size ≤ 0xffff then [code + 0xd0, (size / 0x100).toUInt8, size.toUInt8]
  else [code + 0xe0, (size / 0x1000000).toUInt8, (size / 0x10000).toUInt8, (size / 0x100).toUInt8, size.toUInt8]

mutual
/-- The JSONB of a node: its header and its payload; the payload of an array is the JSONB of
its elements, and that of an object the JSONB of each label and value in order. -/
def encodeNode : JsonNode → List UInt8
  | .null => [0]
  | .true => [1]
  | .false => [2]
  | node@(.int payload) | node@(.int5 payload) | node@(.float payload) | node@(.float5 payload)
  | node@(.text payload) | node@(.textj payload) | node@(.text5 payload) | node@(.textraw payload) =>
    jsonbHeader node.typeCode payload.length ++ payload
  | .array items => let body := encodeItems items; jsonbHeader 11 body.length ++ body
  | .object members => let body := encodeMembers members; jsonbHeader 12 body.length ++ body

/-- The JSONB of the elements of an array, in order. -/
def encodeItems : List JsonNode → List UInt8
  | [] => []
  | item :: rest => encodeNode item ++ encodeItems rest

/-- The JSONB of the members of an object: each label, then its value. -/
def encodeMembers : List (JsonNode × JsonNode) → List UInt8
  | [] => []
  | (label, value) :: rest => encodeNode label ++ encodeNode value ++ encodeMembers rest
end

mutual
/-- The node of valid JSONB at {lit}`index`: the constructor of its node type with its
payload, and the decoded children of an array or an object. -/
def decodeNode (blob : Array UInt8) : Nat → Nat → Option JsonNode
  | 0, _ => none
  | fuel + 1, index =>
    (jsonbHeaderAt blob index).bind fun (headerLength, size) =>
      let start := index + headerLength
      let payload := (blob.extract start (start + size)).toList
      match (byteAt blob index % 16).toNat with
      | 0 => some .null
      | 1 => some .true
      | 2 => some .false
      | 3 => some (.int payload)
      | 4 => some (.int5 payload)
      | 5 => some (.float payload)
      | 6 => some (.float5 payload)
      | 7 => some (.text payload)
      | 8 => some (.textj payload)
      | 9 => some (.text5 payload)
      | 10 => some (.textraw payload)
      | 11 => (decodeItems blob fuel start (start + size)).map JsonNode.array
      | 12 => (decodeMembers blob fuel start (start + size)).map JsonNode.object
      | _ => none

/-- The nodes from {lit}`index` to {lit}`stop`, in order. -/
def decodeItems (blob : Array UInt8) : Nat → Nat → Nat → Option (List JsonNode)
  | 0, _, _ => none
  | fuel + 1, index, stop =>
    if index ≥ stop then some []
    else (jsonbHeaderAt blob index).bind fun (headerLength, size) => do
      let item ← decodeNode blob fuel index
      let rest ← decodeItems blob fuel (index + headerLength + size) stop
      some (item :: rest)

/-- The label and value pairs from {lit}`index` to {lit}`stop`, in order. -/
def decodeMembers (blob : Array UInt8) : Nat → Nat → Nat → Option (List (JsonNode × JsonNode))
  | 0, _, _ => none
  | fuel + 1, index, stop =>
    if index ≥ stop then some []
    else (jsonbHeaderAt blob index).bind fun (headerLength, size) => do
      let label ← decodeNode blob fuel index
      let valueIndex := index + headerLength + size
      let (valueHeader, valueSize) ← jsonbHeaderAt blob valueIndex
      let value ← decodeNode blob fuel valueIndex
      let rest ← decodeMembers blob fuel (valueIndex + valueHeader + valueSize) stop
      some ((label, value) :: rest)
end

/-- How a JSON function reads a BLOB argument. -/
inductive BlobReading where
  /-- The BLOB is not JSONB by the quick check ({name}`isJsonb`), so SQLite reads its bytes as
  JSON text, or, as a value to store, fails with {lit}`JSON cannot hold BLOB values`. -/
  | notJsonb
  /-- Valid JSONB in the encoding that {name}`encodeNode` gives for its tree. -/
  | tree (node : JsonNode)
  /-- JSONB by the quick check that is not valid or not in that encoding: SQLite reads it
  without a full check and edits it in place, which the model does not describe. -/
  | undescribed

/-- Read a BLOB argument: {name}`BlobReading.notJsonb` when the quick check fails, the tree when
the BLOB is valid ({name}`jsonbValid`) and {name}`encodeNode` of the decoded tree gives it back,
else {name}`BlobReading.undescribed`. -/
def readBlob (bytes : List UInt8) : BlobReading :=
  if !isJsonb bytes then .notJsonb
  else
    let blob := bytes.toArray
    if !jsonbValid blob (jsonbFuel blob) 0 blob.size 1 then .undescribed
    else match decodeNode blob (jsonbFuel blob) 0 with
      | some node => if encodeNode node == bytes then .tree node else .undescribed
      | none => .undescribed

end Belay.Sqlite.Model.Json
