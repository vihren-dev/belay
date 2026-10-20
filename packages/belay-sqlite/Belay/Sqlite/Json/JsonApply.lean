import Belay.Sqlite.Json.Functions
import Belay.Sqlite.Json.Valid
import Belay.Sqlite.Json.Build
import Belay.Sqlite.Json.Group
import Belay.Sqlite.Json.PatchPretty
import Belay.Sqlite.Resolution.QueryForm

set_option doc.verso true

/-! The JSON functions of a resolved expression (ADR 0012, amendment 5, slices 6b and 6c;
ADR 0015, slice 3): each {lit}`Resolved.JsonFunction` applied to the values of its arguments
and whether each has SQLite's JSON subtype. -/

namespace Belay.Sqlite.Json

/-- The value of a JSON function over its arguments, or its error. Each argument is a value
and whether it has SQLite's JSON subtype, which only {lit}`json_quote`, {lit}`json_array`,
{lit}`json_object` and the values of the edit functions read.
{lit}`json_extract` takes the JSON and its paths ({name}`extract`); {lit}`->` and
{lit}`->>` take the JSON and one path ({name}`arrowJson`, {name}`arrowValue`);
{lit}`json_type` and {lit}`json_array_length` the JSON and an optional path
({name}`jsonType`, {name}`jsonArrayLength`); {lit}`json_valid` the JSON and optional
flags, 1 without them ({name}`jsonValid`); {lit}`json` the JSON ({name}`jsonText`);
{lit}`json_quote` one value ({name}`sqlValueText`); {lit}`json_array` and {lit}`json_object` any
values ({name}`jsonArray`, {name}`jsonObject`); the edit functions the JSON, then paths and
values ({name}`jsonEdit`, {name}`jsonRemove`); {lit}`json_patch` two JSON values
({name}`jsonPatch`); {lit}`json_pretty` the JSON and an optional indent ({name}`jsonPretty`); and
{lit}`json_error_position` the JSON ({name}`jsonErrorPosition`). Each {lit}`jsonb_*` function
takes the arguments of its {lit}`json_*` form and gives JSONB: {lit}`jsonb` ({name}`jsonbValue`),
{lit}`jsonb_extract` ({name}`jsonbExtract`), the tree of an edit ({name}`nodeOutput`), and the
text of {lit}`json_array` and {lit}`json_object` converted ({name}`textAsJsonb`).
Resolution gives each function a number of arguments that SQLite accepts; any other count
is NULL. For example,
{lean}`apply .arrowValue [(.text "[7]".toUTF8.toList, false), (.integer 0, false)]` is
{lit}`.ok (.integer 7)`. -/
def apply (function : Resolved.JsonFunction) (arguments : List (Value × Bool)) : Except JsonError Value :=
  match function, arguments.map (·.1) with
  | .extract, [] => .ok .null
  | .extract, json :: paths => extract json paths
  | .arrowJson, [json, path] => arrowJson json path
  | .arrowValue, [json, path] => arrowValue json path
  | .typeName, [json] => jsonType json none
  | .typeName, [json, path] => jsonType json (some path)
  | .valid, [json] => jsonValid json (.integer 1)
  | .valid, [json, flags] => jsonValid json flags
  | .arrayLength, [json] => jsonArrayLength json none
  | .arrayLength, [json, path] => jsonArrayLength json (some path)
  | .json, [json] => jsonText json
  | .quote, [value] => (sqlValueText value (arguments.headD (.null, false)).2).map Value.text
  | .array, _ => jsonArray arguments
  | .object, _ => jsonObject arguments
  | .set, _ => jsonEdit Bool.false .set arguments
  | .insert, _ => jsonEdit Bool.false .insert arguments
  | .replace, _ => jsonEdit Bool.false .replace arguments
  | .remove, values => jsonRemove Bool.false values
  | .patch, [target, patch] => jsonPatch Bool.false target patch
  | .jsonb, [json] => jsonbValue json
  | .jsonbExtract, [] => .ok .null
  | .jsonbExtract, json :: paths => jsonbExtract json paths
  | .jsonbArray, _ => (jsonArray arguments).map textAsJsonb
  | .jsonbObject, _ => (jsonObject arguments).map textAsJsonb
  | .jsonbSet, _ => jsonEdit Bool.true .set arguments
  | .jsonbInsert, _ => jsonEdit Bool.true .insert arguments
  | .jsonbReplace, _ => jsonEdit Bool.true .replace arguments
  | .jsonbRemove, values => jsonRemove Bool.true values
  | .jsonbPatch, [target, patch] => jsonPatch Bool.true target patch
  | .pretty, [json] => jsonPretty json none
  | .pretty, [json, indent] => jsonPretty json (some indent)
  | .errorPosition, [json] => jsonErrorPosition json
  | .arrowJson, _ | .arrowValue, _ | .typeName, _ | .valid, _ | .arrayLength, _ | .json, _ | .quote, _
  | .patch, _ | .pretty, _ | .errorPosition, _ | .jsonb, _ | .jsonbPatch, _ => .ok .null

#guard match apply .arrowValue [(.text "[7]".toUTF8.toList, false), (.integer 0, false)] with
  | .ok value => value == .integer 7
  | .error _ => false

end Belay.Sqlite.Json
