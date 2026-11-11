import Belay.Sqlite.Model.Values.Scalar.Values

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Whether SQLite accepts the number of arguments of a JSON function: one or more for
{lit}`json_extract`, exactly two for {lit}`->` and {lit}`->>`, one or two for
{lit}`json_type`, {lit}`json_valid`, {lit}`json_array_length` and {lit}`json_pretty`, exactly one
for {lit}`json`, {lit}`json_quote` and {lit}`json_error_position`, exactly two for
{lit}`json_patch`, and any number for {lit}`json_array`, {lit}`json_object` and the edit
functions, whose own checks follow when they run; each {lit}`jsonb_*` function as its
{lit}`json_*` form. -/
def Resolved.JsonFunction.accepts : Resolved.JsonFunction → Nat → Bool
  | .extract, count | .jsonbExtract, count => count ≥ 1
  | .arrowJson, count | .arrowValue, count | .patch, count | .jsonbPatch, count => count == 2
  | .typeName, count | .valid, count | .arrayLength, count | .pretty, count => count == 1 || count == 2
  | .json, count | .quote, count | .errorPosition, count | .jsonb, count => count == 1
  | .array, _ | .object, _ | .set, _ | .insert, _ | .replace, _ | .remove, _ | .jsonbArray, _ | .jsonbObject, _
  | .jsonbSet, _ | .jsonbInsert, _ | .jsonbReplace, _ | .jsonbRemove, _ => true

end Belay.Sqlite.Model
