import Belay.Sqlite.Json.Path

set_option doc.verso true

/-! The edits of {lit}`json_set`, {lit}`json_insert`, {lit}`json_replace` and {lit}`json_remove` (ADR
0015, slice 3): SQLite 3.51.0's {lit}`jsonLookupStep` with an edit mode ({lit}`JEDIT_DEL`,
{lit}`JEDIT_REPL`, {lit}`JEDIT_INS`, {lit}`JEDIT_SET}`) and {lit}`jsonCreateEditSubstructure`, over the
node tree instead of the JSONB blob. The path syntax and its errors are those of the lookup
({lit}`readPathLabel`, {lit}`readPathIndex`). -/

namespace Belay.Sqlite.Json

/-- What an edit does at the node that the path selects. -/
inductive EditMode where
  /-- {lit}`json_remove`: remove the node, and its label in an object. -/
  | delete
  /-- {lit}`json_replace`: replace the node when it exists. -/
  | replace
  /-- {lit}`json_insert`: add the node when it does not exist. -/
  | insert
  /-- {lit}`json_set`: replace the node, or add it. -/
  | set
  deriving Repr, DecidableEq

/-- Whether the mode adds a missing node ({lit}`eEdit>=JEDIT_INS`). -/
def EditMode.adds : EditMode → Bool
  | .insert | .set => true
  | .delete | .replace => false

/-- The outcome of an edit at one path. -/
inductive EditResult where
  /-- The edited node. -/
  | edited (node : JsonNode)
  /-- The edit removes the node itself (the end of a {lit}`json_remove` path). -/
  | removed
  /-- The path selects nothing, so the edit changes nothing ({lit}`JSON_LOOKUP_NOTFOUND`). -/
  | notFound
  /-- The path has bad syntax ({lit}`JSON_LOOKUP_PATHERROR`). -/
  | pathError
  /-- The JSON is malformed ({lit}`JSON_LOOKUP_ERROR`). -/
  | malformed

mutual
/-- Edit the node at the path from {lit}`position` ({lit}`jsonLookupStep`): at the end of the
path, remove, keep or replace the node by the mode; a {lit}`.label` step edits the member of an
object, and adds a missing one when the mode adds; a {lit}`[N]` step edits the element of an
array, and adds one at the end for {lit}`N` equal to the length when the mode adds. A step on a
node of another kind gives {lit}`notFound`. The fuel bounds the steps. -/
def editStep (path : Array UInt8) (mode : EditMode) (value : JsonNode) : Nat → Nat → JsonNode → EditResult
  | 0, _, _ => .pathError
  | fuel + 1, position, node =>
    let byte := byteAt path position
    if byte == 0 then
      match mode with
      | .delete => .removed
      | .insert => .edited node
      | .replace | .set => .edited value
    else if byte == 46 then
      match readPathLabel path (position + 1) with
      | none => .pathError
      | some (key, rawKey, next) => match node with
        | .object members => editMember path mode value fuel next key rawKey members
        | .null | .true | .false | .int _ | .int5 _ | .float _ | .float5 _ | .text _ | .textj _ | .text5 _
        | .textraw _ | .array _ => .notFound
    else if byte == 91 then
      match node with
      | .array items => match readPathIndex path position items.length with
        | none => .pathError
        | some none => .notFound
        | some (some (index, close)) =>
          if index.toNat < items.length then
            match editStep path mode value fuel (close + 1) (items.getD index.toNat .null) with
            | .edited item => .edited (.array (items.set index.toNat item))
            | .removed => .edited (.array (items.eraseIdx index.toNat))
            | .notFound => .notFound
            | .pathError => .pathError
            | .malformed => .malformed
          else if index.toNat == items.length && mode.adds then
            match createSubstructure path mode value fuel (close + 1) with
            | .edited item => .edited (.array (items ++ [item]))
            | .removed | .notFound => .notFound
            | .pathError => .pathError
            | .malformed => .malformed
          else .notFound
      | .null | .true | .false | .int _ | .int5 _ | .float _ | .float5 _ | .text _ | .textj _ | .text5 _
      | .textraw _ | .object _ => .notFound
    else .pathError

/-- Edit the member of an object whose label matches the key ({lit}`labelsMatch`), or add the
member at the end with the label as written ({lit}`JSONB_TEXTRAW` without escapes, else
{lit}`JSONB_TEXT5`) when no label matches and the mode adds. -/
def editMember (path : Array UInt8) (mode : EditMode) (value : JsonNode) :
    Nat → Nat → List UInt8 → Bool → List (JsonNode × JsonNode) → EditResult
  | 0, _, _, _, _ => .pathError
  | fuel + 1, next, key, rawKey, members =>
  match members.findIdx? fun (label, _) => (label.labelText.map fun (text, raw) => labelsMatch key rawKey text raw).getD false with
  | some index =>
    match editStep path mode value fuel next ((members.getD index (.null, .null)).2) with
    | .edited item => .edited (.object (members.set index ((members.getD index (.null, .null)).1, item)))
    | .removed => .edited (.object (members.eraseIdx index))
    | .notFound => .notFound
    | .pathError => .pathError
    | .malformed => .malformed
  | none =>
    if members.any (fun (label, _) => label.labelText.isNone) then .malformed
    else if mode.adds then
      match createSubstructure path mode value fuel next with
      | .edited item => .edited (.object (members ++ [(if rawKey then .textraw key else .text5 key, item)]))
      | .removed | .notFound => .notFound
      | .pathError => .pathError
      | .malformed => .malformed
    else .notFound

/-- The node that a missing step adds ({lit}`jsonCreateEditSubstructure`): the value at the end
of the path, else an empty object for a {lit}`.` step or an empty array otherwise, edited by the
rest of the path. -/
def createSubstructure (path : Array UInt8) (mode : EditMode) (value : JsonNode) : Nat → Nat → EditResult
  | 0, _ => .pathError
  | fuel + 1, position =>
  if byteAt path position == 0 then .edited value
  else editStep path mode value fuel position (if byteAt path position == 46 then .object [] else .array [])
end

/-- Edit a whole document at a path text that starts after its {lit}`$`
({name}`editStep` with fuel for every step: each step of the path uses at most three calls). -/
def editPath (mode : EditMode) (value : JsonNode) (path : List UInt8) (root : JsonNode) : EditResult :=
  editStep path.toArray mode value (3 * path.length + 6) 0 root

end Belay.Sqlite.Json
