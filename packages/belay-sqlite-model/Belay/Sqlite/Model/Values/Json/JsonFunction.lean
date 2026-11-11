import Belay.Sqlite.Model.Shared.Resolved.JsonFunction

set_option doc.verso true

/-! The JSON functions that a resolved expression calls (ADR 0012, amendment 5, slices 6b
and 6c; ADR 0015, slice 3). -/

namespace Belay.Sqlite.Model.Resolved

/-- Whether a call of the function gives a value with SQLite's JSON subtype whatever it
selects: {lit}`json`, {lit}`->`, {lit}`json_quote`, {lit}`json_array`, {lit}`json_object` and the edit
functions. {lit}`json_extract` gives it only for an array or an object, or with two or more
paths, which evaluation decides; the other functions give plain values, and a {lit}`jsonb_*`
function gives a BLOB without the subtype. -/
def JsonFunction.givesJson : JsonFunction → Bool
  | .json | .arrowJson | .quote | .array | .object | .set | .insert | .replace | .remove | .patch => true
  | .extract | .arrowValue | .typeName | .valid | .arrayLength | .pretty | .errorPosition | .jsonb | .jsonbExtract
  | .jsonbArray | .jsonbObject | .jsonbSet | .jsonbInsert | .jsonbReplace | .jsonbRemove | .jsonbPatch => false

/-- The positions of the arguments that the function writes as SQL values, whose JSON subtype
decides whether they are JSON or text ({lit}`jsonAppendSqlValue`, {lit}`jsonFunctionArgToBlob`): every
argument of {lit}`json_quote` and {lit}`json_array`, the values of {lit}`json_object`, and the values
after each path of the edit functions; none for the other functions. -/
def JsonFunction.valuePositions (function : JsonFunction) (count : Nat) : List Nat :=
  match function with
  | .quote | .array | .jsonbArray => List.range count
  | .object | .jsonbObject => (List.range count).filter (· % 2 == 1)
  | .set | .insert | .replace | .jsonbSet | .jsonbInsert | .jsonbReplace =>
    (List.range count).filter fun position => position ≥ 2 && position % 2 == 0
  | .extract | .arrowJson | .arrowValue | .typeName | .valid | .arrayLength | .json | .remove | .patch | .pretty
  | .errorPosition | .jsonb | .jsonbExtract | .jsonbRemove | .jsonbPatch => []

end Belay.Sqlite.Model.Resolved
