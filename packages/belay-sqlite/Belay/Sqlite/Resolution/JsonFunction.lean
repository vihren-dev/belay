import Belay.Sqlite.Declarations

set_option doc.verso true

/-! The JSON functions that a resolved expression calls (ADR 0012, amendment 5, slices 6b
and 6c; ADR 0015, slice 3). -/

namespace Belay.Sqlite.Resolved

/-- A JSON function of ADR 0012, amendment 5, slices 6b and 6c: {lit}`json_extract`, the
operators {lit}`->` and {lit}`->>`, which SQLite's parser makes calls of the functions
{lit}`->` and {lit}`->>`, {lit}`json_type`, {lit}`json_valid`, {lit}`json_array_length`
and {lit}`json`. -/
inductive JsonFunction where
  /-- {lit}`json_extract(json, path, ...)`. -/
  | extract
  /-- {lit}`json -> path`: the selection as JSON text. -/
  | arrowJson
  /-- {lit}`json ->> path`: the selection as an SQL value. -/
  | arrowValue
  /-- {lit}`json_type(json [, path])`: the JSON type name. -/
  | typeName
  /-- {lit}`json_valid(json [, flags])`: 1 or 0. -/
  | valid
  /-- {lit}`json_array_length(json [, path])`: the number of elements. -/
  | arrayLength
  /-- {lit}`json(json)`: the rendered JSON text. -/
  | json
  /-- {lit}`json_quote(x)`: the SQL value as JSON. -/
  | quote
  /-- {lit}`json_array(x, ...)`. -/
  | array
  /-- {lit}`json_object(label, value, ...)`. -/
  | object
  /-- {lit}`json_set(json, path, value, ...)`: replace or add. -/
  | set
  /-- {lit}`json_insert(json, path, value, ...)`: add when missing. -/
  | insert
  /-- {lit}`json_replace(json, path, value, ...)`: replace when present. -/
  | replace
  /-- {lit}`json_remove(json, path, ...)`. -/
  | remove
  /-- {lit}`json_patch(target, patch)`: the RFC 7396 merge patch. -/
  | patch
  /-- {lit}`json_pretty(json [, indent])`. -/
  | pretty
  /-- {lit}`json_error_position(json)`. -/
  | errorPosition
  deriving Repr, DecidableEq

/-- Whether a call of the function gives a value with SQLite's JSON subtype whatever it
selects: {lit}`json`, {lit}`->`, {lit}`json_quote`, {lit}`json_array`, {lit}`json_object` and the edit
functions. {lit}`json_extract` gives it only for an array or an object, or with two or more
paths, which evaluation decides; the other functions give plain values. -/
def JsonFunction.givesJson : JsonFunction → Bool
  | .json | .arrowJson | .quote | .array | .object | .set | .insert | .replace | .remove | .patch => true
  | .extract | .arrowValue | .typeName | .valid | .arrayLength | .pretty | .errorPosition => false

/-- The positions of the arguments that the function writes as SQL values, whose JSON subtype
decides whether they are JSON or text ({lit}`jsonAppendSqlValue`, {lit}`jsonFunctionArgToBlob`): every
argument of {lit}`json_quote` and {lit}`json_array`, the values of {lit}`json_object`, and the values
after each path of the edit functions; none for the other functions. -/
def JsonFunction.valuePositions (function : JsonFunction) (count : Nat) : List Nat :=
  match function with
  | .quote | .array => List.range count
  | .object => (List.range count).filter (· % 2 == 1)
  | .set | .insert | .replace => (List.range count).filter fun position => position ≥ 2 && position % 2 == 0
  | .extract | .arrowJson | .arrowValue | .typeName | .valid | .arrayLength | .json | .remove | .patch | .pretty
  | .errorPosition => []

end Belay.Sqlite.Resolved
