import Belay.Sqlite.Model.Json.Jsonb
import Belay.Sqlite.Model.Json.Extract
import Belay.Sqlite.Model.Json.Functions

set_option doc.verso true

/-! The JSONB results of the {lit}`jsonb_*` functions (ADR 0015, slice 4), from SQLite 3.51.0's
{lit}`jsonReturnParse` and {lit}`jsonReturnStringAsBlob`: a function that edits a tree gives its
JSONB ({lit}`encodeNode`), and a function that writes JSON text, such as {lit}`jsonb_array`,
converts the text, so a string is {lit}`TEXT` or {lit}`TEXTJ` and never {lit}`TEXTRAW`. -/

namespace Belay.Sqlite.Model.Json

open Belay.Sqlite.Model

/-- The result of a function from its tree: JSON text ({name}`renderNode`), or JSONB
({name}`encodeNode`) for a {lit}`jsonb_*` function ({lit}`binary`). -/
def nodeOutput (binary : Bool) (node : JsonNode) : Value :=
  if binary then .blob (encodeNode node) else .text (renderNode node)

/-- A result of JSON text as JSONB ({lit}`jsonReturnStringAsBlob`): TEXT becomes the JSONB of
its tree; another value, such as NULL, stays. -/
def textAsJsonb : Value → Value
  | .text bytes => match parseJsonText bytes with
    | some node => .blob (encodeNode node)
    | none => .text bytes
  | value@(.null) | value@(.integer _) | value@(.real _) | value@(.blob _) => value

/-- {lit}`jsonb(json)` ({lit}`jsonbFunc`): the JSONB of the argument's tree, NULL for NULL. A JSONB
argument that the model reads is its own encoding, so it comes back unchanged. -/
def jsonbValue (json : Value) : Except JsonError Value :=
  selectedValue (selectNode json none) (nodeOutput Bool.true)

/-- {lit}`jsonb_extract(json, path, ...)` ({lit}`jsonExtractFunc` with {lit}`JSON_BLOB`): with one
path, the JSONB of a selected array or object and the SQL value of another node, as
{name}`extract` gives it; with no path NULL; with several paths the JSON array text of
{name}`extract` as JSONB. -/
def jsonbExtract (json : Value) (paths : List Value) : Except JsonError Value :=
  match paths with
  | [path] =>
    match parseJsonArgument json with
    | .error error => .error error
    | .ok none => .ok .null
    | .ok (some node) =>
      match valueText path with
      | none => .ok .null
      | some pathBytes =>
        match lookupFullPath node pathBytes with
        | .error error => .error error
        | .ok none => .ok .null
        | .ok (some found@(.array _)) | .ok (some found@(.object _)) => .ok (.blob (encodeNode found))
        | .ok (some found@.null) | .ok (some found@.true) | .ok (some found@.false) | .ok (some found@(.int _))
        | .ok (some found@(.int5 _)) | .ok (some found@(.float _)) | .ok (some found@(.float5 _))
        | .ok (some found@(.text _)) | .ok (some found@(.textj _)) | .ok (some found@(.text5 _))
        | .ok (some found@(.textraw _)) => sqlValueOfNode found
  | [] | _ :: _ :: _ => (extract json paths).map textAsJsonb

end Belay.Sqlite.Model.Json
