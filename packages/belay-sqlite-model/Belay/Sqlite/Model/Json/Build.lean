import Belay.Sqlite.Model.Json.Edit
import Belay.Sqlite.Model.Json.Extract
import Belay.Sqlite.Model.Json.Render
import Belay.Sqlite.Model.Json.JsonbOutput
import Belay.Sqlite.Model.Arithmetic

set_option doc.verso true

/-! The JSON functions that build or edit text (ADR 0015, slice 3), from SQLite 3.51.0's JSON
code: {lit}`json_quote`, {lit}`json_array`, {lit}`json_object`, {lit}`json_set`, {lit}`json_insert`,
{lit}`json_replace` and {lit}`json_remove` ({lit}`json_patch`, {lit}`json_pretty` and
{lit}`json_error_position` are in {lit}`Json.PatchPretty`). An argument comes with whether it
has SQLite's JSON subtype, which decides whether it is JSON or text. A BLOB value is JSONB ({lit}`readBlob`), or fails with
{lit}`JSON cannot hold BLOB values` when it is not JSONB by SQLite's quick check. -/

namespace Belay.Sqlite.Model.Json

open Belay.Sqlite.Model

/-- The tree of a BLOB value that a JSON function stores ({lit}`jsonArgIsJsonb` in
{lit}`jsonAppendSqlValue` and {lit}`jsonFunctionArgToBlob`): the tree of JSONB that the model
reads, {lit}`JSON cannot hold BLOB values` for a BLOB that is not JSONB, and
{lit}`blobArgument` for JSONB that the model does not describe. -/
def blobValueNode (bytes : List UInt8) : Except JsonError JsonNode :=
  match readBlob bytes with
  | .tree node => .ok node
  | .notJsonb => .error .blobValue
  | .undescribed => .error .blobArgument

/-- A double as JSON text ({lit}`%!0.15g` of {lit}`jsonAppendSqlValue`): an infinity is
{lit}`9.0e+999` under the {lit}`0` flag, with a minus sign when negative. -/
def jsonDoubleText (value : Float) : List UInt8 :=
  if value.isInf then (if value < 0 then [45] else []) ++ "9.0e+999".toUTF8.toList else formatGeneral 15 true value

/-- An SQL value as JSON text ({lit}`jsonAppendSqlValue`): NULL as {lit}`null`, an integer in
decimal, a REAL by {name}`jsonDoubleText`, JSON text as it is, other text as a JSON string
({name}`escapeSqlText`), a JSONB BLOB as the text of its tree, and the error
{lit}`JSON cannot hold BLOB values` for another BLOB. -/
def sqlValueText (value : Value) (json : Bool) : Except JsonError (List UInt8) :=
  match value with
  | .null => .ok "null".toUTF8.toList
  | .integer _ => .ok value.textBytes
  | .real bits => .ok (jsonDoubleText (Float.ofBits bits))
  | .text bytes => .ok (if json then bytes else quoted (escapeSqlText bytes))
  | .blob bytes => (blobValueNode bytes).map renderNode

/-- An SQL value as a JSON node to insert ({lit}`jsonFunctionArgToBlob`): NULL as {lit}`null`, an
integer as its decimal text, a REAL as its text ({lit}`9e999` for an infinity), JSON text
parsed (malformed text fails), other text as {lit}`textraw`, and a BLOB as its JSONB tree
({name}`blobValueNode`). -/
def sqlValueNode (value : Value) (json : Bool) : Except JsonError JsonNode :=
  match value with
  | .null => .ok .null
  | .integer _ => .ok (.int value.textBytes)
  | .real bits =>
    let text := realText (Float.ofBits bits)
    .ok (.float (if text.headD 0 == 73 then "9e999".toUTF8.toList
      else if text.take 2 == [45, 73] then "-9e999".toUTF8.toList else text))
  | .text bytes => if json then (match parseJsonText bytes with
      | some node => .ok node
      | none => .error .malformed) else .ok (.textraw bytes)
  | .blob bytes => blobValueNode bytes

/-- The texts of SQL values as JSON, in order ({name}`sqlValueText`). -/
def sqlValueTexts : List (Value × Bool) → Except JsonError (List (List UInt8))
  | [] => .ok []
  | (value, json) :: rest => do
    let first ← sqlValueText value json
    let later ← sqlValueTexts rest
    .ok (first :: later)

/-- {lit}`json_array(x, ...)`: the JSON array of the arguments ({lit}`jsonArrayFunc`). -/
def jsonArray (arguments : List (Value × Bool)) : Except JsonError Value :=
  (sqlValueTexts arguments).map fun items => .text ([91] ++ List.intercalate [44] items ++ [93])

/-- The members of {lit}`json_object`: each label must be TEXT, and is written as a JSON string;
each value as {name}`sqlValueText`. -/
def objectMembers : List (Value × Bool) → Except JsonError (List (List UInt8))
  | [] => .ok []
  | [_] => .error .objectArgumentCount
  | (label, _) :: (value, json) :: rest => match label with
    | .text bytes => do
      let text ← sqlValueText value json
      let later ← objectMembers rest
      .ok ((quoted (escapeSqlText bytes) ++ [58] ++ text) :: later)
    | .null | .integer _ | .real _ | .blob _ => .error .labelNotText

/-- {lit}`json_object(label, value, ...)` ({lit}`jsonObjectFunc`): an odd number of arguments
fails, then the members in order. -/
def jsonObject (arguments : List (Value × Bool)) : Except JsonError Value :=
  if arguments.length % 2 == 1 then .error .objectArgumentCount
  else (objectMembers arguments).map fun members => .text ([123] ++ List.intercalate [44] members ++ [125])

/-- The path text after its {lit}`$`, or the bad path error of a text that does not start with
{lit}`$`. -/
def pathTail (path : List UInt8) : Except JsonError (List UInt8) :=
  match path with
  | 36 :: rest => .ok rest
  | _ => .error (.badPath path)

/-- Apply the path and value pairs of an edit in turn ({lit}`jsonInsertIntoBlob`): a NULL path is
skipped; the value becomes a node; {lit}`$` alone replaces the root for {lit}`json_set` and
{lit}`json_replace`; another path edits the node ({name}`editPath`), and a path that selects
nothing changes nothing. -/
def applyEdits (mode : EditMode) (root : JsonNode) : List (Value × Bool) → Except JsonError JsonNode
  | [] | [_] => .ok root
  | (path, _) :: (value, json) :: rest =>
    match valueText path with
    | none => if path.isNull then applyEdits mode root rest else .error .malformed
    | some pathBytes => do
      let tail ← pathTail pathBytes
      let node ← sqlValueNode value json
      if tail.isEmpty then applyEdits mode (if mode == .insert then root else node) rest
      else match editPath mode node tail root with
        | .edited edited => applyEdits mode edited rest
        | .removed | .notFound => applyEdits mode root rest
        | .pathError => .error (.badPath pathBytes)
        | .malformed => .error .malformed

/-- The name of the function of an edit after {lit}`json_`, as its errors name it. -/
def EditMode.functionName : EditMode → List UInt8
  | .delete => "remove".toUTF8.toList
  | .replace => "replace".toUTF8.toList
  | .insert => "insert".toUTF8.toList
  | .set => "set".toUTF8.toList

/-- {lit}`json_set`, {lit}`json_insert` and {lit}`json_replace` ({lit}`jsonSetFunc`,
{lit}`jsonReplaceFunc`): an even number of arguments fails, a NULL JSON gives NULL, then the
edits of {name}`applyEdits` and the result as text, or as JSONB for {lit}`binary`
({name}`nodeOutput`). -/
def jsonEdit (binary : Bool) (mode : EditMode) (arguments : List (Value × Bool)) : Except JsonError Value :=
  match arguments with
  | [] => .ok .null
  | (json, _) :: rest =>
    if arguments.length % 2 == 0 then .error (.editArgumentCount mode.functionName)
    else match parseJsonArgument json with
      | .error error => .error error
      | .ok none => .ok .null
      | .ok (some root) => (applyEdits mode root rest).map (nodeOutput binary)

/-- The removals of {lit}`json_remove` in turn ({lit}`jsonRemoveFunc`): a NULL path or {lit}`$` alone
ends with NULL; a path that selects nothing changes nothing. -/
def applyRemovals (root : JsonNode) : List Value → Except JsonError (Option JsonNode)
  | [] => .ok (some root)
  | path :: rest =>
    match valueText path with
    | none => .ok none
    | some pathBytes => do
      let tail ← pathTail pathBytes
      if tail.isEmpty then .ok none
      else match editPath .delete .null tail root with
        | .edited edited => applyRemovals edited rest
        | .removed => .ok none
        | .notFound => applyRemovals root rest
        | .pathError => .error (.badPath pathBytes)
        | .malformed => .error .malformed

/-- {lit}`json_remove(json, path, ...)`: NULL without arguments or for a NULL JSON, else the result
of {name}`applyRemovals` as text, or as JSONB for {lit}`binary`. -/
def jsonRemove (binary : Bool) (arguments : List Value) : Except JsonError Value :=
  match arguments with
  | [] => .ok .null
  | json :: paths => match parseJsonArgument json with
    | .error error => .error error
    | .ok none => .ok .null
    | .ok (some root) => (applyRemovals root paths).map fun
      | some node => nodeOutput binary node
      | none => .null

end Belay.Sqlite.Model.Json
