import Belay.Sqlite.Json.Extract
import Belay.Sqlite.Json.Render

set_option doc.verso true

/-! The JSON functions {lit}`json_patch`, {lit}`json_pretty` and {lit}`json_error_position`
(ADR 0015, slice 3), from SQLite 3.51.0's JSON code, over the node tree of their JSON
arguments. -/

namespace Belay.Sqlite.Json

open Belay.Sqlite

mutual
/-- SQLite's RFC 7396 merge patch of a target ({lit}`jsonMergePatch`): a patch that is no object
replaces the target; else the target becomes an object (an empty one when it is not), and
each member of the patch in order removes the first target member with the same label when
its value is {lit}`null`, merges into it when it exists, and else is added at the end, merged
into {lit}`null` when it is an object. The fuel bounds the calls: each node of the patch uses
at most two, and its text has a byte for each node. -/
def mergePatch : Nat → JsonNode → JsonNode → JsonNode
  | 0, target, _ => target
  | fuel + 1, target, patch => match patch with
    | .object patchMembers =>
      let members := match target with
        | .object members => members
        | .null | .true | .false | .int _ | .int5 _ | .float _ | .float5 _ | .text _ | .textj _ | .text5 _
        | .textraw _ | .array _ => []
      .object (mergeMembers fuel members patchMembers)
    | .null | .true | .false | .int _ | .int5 _ | .float _ | .float5 _ | .text _ | .textj _ | .text5 _
    | .textraw _ | .array _ => patch

/-- The members of a target object after each member of a patch in order ({name}`mergePatch`). -/
def mergeMembers : Nat → List (JsonNode × JsonNode) → List (JsonNode × JsonNode) → List (JsonNode × JsonNode)
  | 0, members, _ => members
  | _, members, [] => members
  | fuel + 1, members, (label, value) :: rest =>
    let same := fun (other : JsonNode × JsonNode) => match label.labelText, other.1.labelText with
      | some (text, raw), some (otherText, otherRaw) => labelsMatch text raw otherText otherRaw
      | some _, none | none, _ => false
    let members := match members.findIdx? same, value with
      | some index, .null => members.eraseIdx index
      | some index, _ => members.set index ((members.getD index (.null, .null)).1,
          mergePatch fuel (members.getD index (.null, .null)).2 value)
      | none, .null => members
      | none, .object _ => members ++ [(label, mergePatch fuel .null value)]
      | none, _ => members ++ [(label, value)]
    mergeMembers fuel members rest
end

/-- {lit}`json_patch(target, patch)` ({lit}`jsonPatchFunc`): NULL for a NULL argument, else the text of
{name}`mergePatch`. -/
def jsonPatch (target patch : Value) : Except JsonError Value := do
  let target ← parseJsonArgument target
  let patch ← parseJsonArgument patch
  match target, patch with
  | some target, some patch =>
    .ok (.text (renderNode (mergePatch (2 * (renderNode patch).length + 2) target patch)))
  | none, _ | some _, none => .ok .null

mutual
/-- The pretty text of a node ({lit}`jsonTranslateBlobToPrettyText`) at a nesting level: an array or
an object with each element or member on its own line, indented once per level, members as
{lit}`label: value`; an empty one as {lit}`[]` or {lit}`{}`; other nodes as {name}`renderNode`. -/
def prettyNode (indent : List UInt8) (level : Nat) : JsonNode → List UInt8
  | .array [] => [91, 93]
  | .array items => [91, 10] ++ prettyItems indent (level + 1) items ++ [10] ++ List.flatten (List.replicate level indent) ++ [93]
  | .object [] => [123, 125]
  | .object members =>
    [123, 10] ++ prettyMembers indent (level + 1) members ++ [10] ++ List.flatten (List.replicate level indent) ++ [125]
  | node@(.null) | node@(.true) | node@(.false) | node@(.int _) | node@(.int5 _) | node@(.float _)
  | node@(.float5 _) | node@(.text _) | node@(.textj _) | node@(.text5 _) | node@(.textraw _) => renderNode node

/-- The elements of an array, each indented, separated by {lit}`,` and a new line. -/
def prettyItems (indent : List UInt8) (level : Nat) : List JsonNode → List UInt8
  | [] => []
  | [item] => List.flatten (List.replicate level indent) ++ prettyNode indent level item
  | item :: rest => List.flatten (List.replicate level indent) ++ prettyNode indent level item ++ [44, 10] ++
      prettyItems indent level rest

/-- The members of an object, each indented as {lit}`label: value`, separated by {lit}`,` and a new
line. -/
def prettyMembers (indent : List UInt8) (level : Nat) : List (JsonNode × JsonNode) → List UInt8
  | [] => []
  | [(label, value)] => List.flatten (List.replicate level indent) ++ renderNode label ++ [58, 32] ++
      prettyNode indent level value
  | (label, value) :: rest => List.flatten (List.replicate level indent) ++ renderNode label ++ [58, 32] ++
      prettyNode indent level value ++ [44, 10] ++ prettyMembers indent level rest
end

/-- {lit}`json_pretty(json [, indent])` ({lit}`jsonPrettyFunc`): NULL for NULL JSON; the indent is
four spaces without an argument or for NULL, else the C string of the argument. -/
def jsonPretty (json : Value) (indent : Option Value) : Except JsonError Value :=
  match parseJsonArgument json with
  | .error error => .error error
  | .ok none => .ok .null
  | .ok (some node) =>
    let indent := match indent.bind valueText with
      | some bytes => bytes.takeWhile (· != 0)
      | none => [32, 32, 32, 32]
    .ok (.text (prettyNode indent 0 node))

/-- {lit}`json_error_position(json)` ({lit}`jsonErrorFunc`): NULL for NULL, 0 for well-formed JSON
text; the position of an error in malformed text is not described ({lit}`unmodeledPosition`). -/
def jsonErrorPosition (json : Value) : Except JsonError Value :=
  match parseJsonArgument json with
  | .ok none => .ok .null
  | .ok (some _) => .ok (.integer 0)
  | .error .malformed => .error .unmodeledPosition
  | .error error => .error error

end Belay.Sqlite.Json
