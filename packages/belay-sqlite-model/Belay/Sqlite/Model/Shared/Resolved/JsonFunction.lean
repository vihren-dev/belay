import Belay.Sqlite.Model.Shared.Values.Declarations

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- A JSON function of ADR 0012, amendment 5, slices 6b and 6c, and of ADR 0015, slices 3 and 4: {lit}`json_extract`, the
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
  /-- {lit}`jsonb(json)`: the JSONB of the argument. -/
  | jsonb
  /-- {lit}`jsonb_extract(json, path, ...)`: a selected array or object as JSONB. -/
  | jsonbExtract
  /-- {lit}`jsonb_array(x, ...)`. -/
  | jsonbArray
  /-- {lit}`jsonb_object(label, value, ...)`. -/
  | jsonbObject
  /-- {lit}`jsonb_set(json, path, value, ...)`. -/
  | jsonbSet
  /-- {lit}`jsonb_insert(json, path, value, ...)`. -/
  | jsonbInsert
  /-- {lit}`jsonb_replace(json, path, value, ...)`. -/
  | jsonbReplace
  /-- {lit}`jsonb_remove(json, path, ...)`. -/
  | jsonbRemove
  /-- {lit}`jsonb_patch(target, patch)`. -/
  | jsonbPatch
  deriving Repr, DecidableEq

end Belay.Sqlite.Model.Resolved
