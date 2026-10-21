import Belay.Sqlite.Model.Json.Build

set_option doc.verso true

/-! The JSON aggregates {lit}`json_group_array` and {lit}`json_group_object` (ADR 0015, slice 3)
and their JSONB forms (slice 4), from SQLite 3.51.0's {lit}`jsonArrayStep` and
{lit}`jsonObjectStep`: each writes the values of its group as {lit}`json_array` does. -/

namespace Belay.Sqlite.Model.Json

open Belay.Sqlite.Model

/-- {lit}`json_group_array(x)` over the values of a group ({lit}`jsonArrayStep`): the array of
{name}`jsonArray`; a value that the model does not describe (a BLOB) gives NULL, with the
fault of its operand ({lit}`Output.operands`). -/
def groupArray (values : List (Value × Bool)) : Value :=
  match jsonArray values with
  | .ok array => array
  | .error _ => .null

/-- The members of {lit}`json_group_object` ({lit}`jsonObjectStep`): a row with a NULL label adds
none; a label is its text up to the first NUL byte as a JSON string, then the value as
{name}`sqlValueText`. -/
def groupMembers : List (Value × Value × Bool) → Except JsonError (List (List UInt8))
  | [] => .ok []
  | (label, value, json) :: rest => match valueText label with
    | none => groupMembers rest
    | some bytes => do
      let text ← sqlValueText value json
      let later ← groupMembers rest
      .ok ((quoted (escapeSqlText (cString bytes)) ++ [58] ++ text) :: later)

/-- {lit}`json_group_object(label, value)` over the rows of a group: the object of
{name}`groupMembers`; NULL with the fault of the value operand when a value is one that the
model does not describe. -/
def groupObject (rows : List (Value × Value × Bool)) : Value :=
  match groupMembers rows with
  | .ok members => .text ([123] ++ List.intercalate [44] members ++ [125])
  | .error _ => .null

/-- The result of a JSON aggregate: its text, or for {lit}`jsonb_group_array` and
{lit}`jsonb_group_object` ({lit}`binary`) that text as JSONB ({name}`textAsJsonb`), as
{lit}`jsonArrayCompute` returns it. -/
def groupOutput (binary : Bool) (value : Value) : Value := if binary then textAsJsonb value else value

end Belay.Sqlite.Model.Json
