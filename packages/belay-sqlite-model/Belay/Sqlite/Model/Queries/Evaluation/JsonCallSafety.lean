import Belay.Sqlite.Model.Queries.Evaluation.JsonPathSafety

set_option doc.verso true

/-! Input conditions for the JSON and JSONB scalar functions, with SQLite subtype flags. -/

namespace Belay.Sqlite.Model.Resolved.CallSafety
open Json

/-- Input conditions for {name}`Json.apply`, on values paired with their JSON subtype flags:
* JSON and JSONB extraction require {name}`ExtractInputs` on the document and path list.
* Both arrows require a successful lookup. The SQL-value arrow also requires conversion
  of each found node to an SQL value.
* Type and array length require successful selection with their optional path. JSON and
  JSONB conversion require selection of the document root.
* One-argument validation accepts every value. With two arguments the flags must be accepted.
* Quote requires conversion to JSON text with the original subtype flag. Array constructors
  require all elements to convert. Object constructors require an even argument count and
  successful construction of the members. Both encodings use the same checks.
* Set, insert and replace require {name}`EditInputs` for the corresponding mode. Remove
  requires {name}`RemoveInputs`. Patch requires both input documents to parse.
* Pretty with either arity and error position require the document to parse.
* Extraction with no arguments and the remaining default arities require no evidence.
  These arity defaults describe the evaluator after the separate resolution check. -/
def JsonInputs (f : JsonFunction) (args : List (Value × Bool)) : Prop :=
  match f, args.map (·.1) with
  | .extract, v :: paths | .jsonbExtract, v :: paths => ExtractInputs v paths
  | .arrowJson, [v, p] => Returns (arrowSelect v p)
  | .arrowValue, [v, p] => Returns (arrowSelect v p) ∧
      ∀ n, arrowSelect v p = .ok (some n) → Returns (sqlValueOfNode n)
  | .typeName, [v] | .arrayLength, [v] | .json, [v] | .jsonb, [v] => Returns (selectNode v none)
  | .typeName, [v, p] | .arrayLength, [v, p] => Returns (selectNode v (some p))
  | .valid, [_] => True
  | .valid, [_, flags] => flagsAccepted (flagsValue flags) = true
  | .quote, [v] => Returns (sqlValueText v (args.headD (.null, false)).2)
  | .array, _ | .jsonbArray, _ => Returns (sqlValueTexts args)
  | .object, _ | .jsonbObject, _ => args.length % 2 ≠ 1 ∧ Returns (objectMembers args)
  | .set, _ | .jsonbSet, _ => EditInputs .set args
  | .insert, _ | .jsonbInsert, _ => EditInputs .insert args
  | .replace, _ | .jsonbReplace, _ => EditInputs .replace args
  | .remove, vs | .jsonbRemove, vs => RemoveInputs vs
  | .patch, [v, w] | .jsonbPatch, [v, w] => Returns (parseJsonArgument v) ∧ Returns (parseJsonArgument w)
  | .pretty, [v] | .pretty, [v, _] | .errorPosition, [v] => Returns (parseJsonArgument v)
  | .extract, [] | .jsonbExtract, [] | .arrowJson, _ | .arrowValue, _ | .typeName, _ | .valid, _
  | .arrayLength, _ | .json, _ | .quote, _ | .patch, _ | .jsonbPatch, _ | .jsonb, _
  | .pretty, _ | .errorPosition, _ => True

/-- A successful document selection yields NULL or a rendered value. Substitute the selection. -/
private theorem selected_ok {s} (fn : JsonNode → Value) (h : Returns s) : Returns (selectedValue s fn) := by
  obtain ⟨v, eq⟩ := h
  cases v <;> simp [Returns, selectedValue, eq]

/-- Accepted flags give a validation result for every storage class. Reduce the flag check
and inspect the value, including the separate JSONB detection branch. -/
private theorem valid_ok (v flags : Value) (ok : flagsAccepted (flagsValue flags) = true) :
    Returns (jsonValid v flags) := by
  cases v <;> simp [Returns, jsonValid, ok] <;> split <;> exact ⟨_, rfl⟩

/-- Successful edits, with an odd argument count, can return text or JSONB.
Substitute the parse result and map the edited root into the chosen encoding. -/
private theorem edit_ok (b : Bool) (mode : EditMode) (args) (h : EditInputs mode args) :
    Returns (jsonEdit b mode args) := by
  cases args with
  | nil => exact ⟨_, rfl⟩
  | cons a rest =>
    obtain ⟨count, ⟨root, eq⟩, edits⟩ := h
    cases root with
    | none => simp [Returns, jsonEdit, count, eq]
    | some n => simpa [jsonEdit, count, eq] using map_ok (nodeOutput b) (edits n eq)

/-- If removal inputs are ready, JSON removal returns text or JSONB. Substitute the
parsed document and map the remaining optional root to its result. -/
private theorem remove_ok (b : Bool) (vs) (h : RemoveInputs vs) : Returns (jsonRemove b vs) := by
  cases vs with
  | nil => exact ⟨_, rfl⟩
  | cons v paths =>
    obtain ⟨⟨root, eq⟩, remove⟩ := h
    cases root with
    | none => simp [Returns, jsonRemove, eq]
    | some n =>
      obtain ⟨out, good⟩ := remove n eq
      simp [Returns, jsonRemove, eq, good, Except.map]

/-- Even length and successful construction of the members give a JSON object.
Rewrite the length check and map the members to the object text. -/
private theorem object_ok (args) (h : args.length % 2 ≠ 1 ∧ Returns (objectMembers args)) :
    Returns (jsonObject args) := by
  unfold jsonObject
  simp [h.1]
  exact map_ok _ h.2

/-- Two successfully parsed documents give a patch result, including NULL.
Substitute both results in the two parse steps. -/
private theorem patch_ok (b : Bool) (v w : Value)
    (h : Returns (parseJsonArgument v) ∧ Returns (parseJsonArgument w)) :
    Returns (jsonPatch b v w) := by
  obtain ⟨⟨n, eq⟩, ⟨m, eq'⟩⟩ := h
  cases n <;> cases m <;> simp [Returns, jsonPatch, eq, eq', Bind.bind, Except.bind]

/-- A parsed document has a pretty-printed result for any indent. Substitute its root. -/
private theorem pretty_ok (v indent) (ok : Returns (parseJsonArgument v)) : Returns (jsonPretty v indent) := by
  obtain ⟨n, eq⟩ := ok
  cases n <;> simp [Returns, jsonPretty, eq]

/-- A successfully parsed document has an error-position result. Substitute the parse result. -/
private theorem position_ok (v) (ok : Returns (parseJsonArgument v)) : Returns (jsonErrorPosition v) := by
  obtain ⟨n, eq⟩ := ok
  cases n <;> simp [Returns, jsonErrorPosition, eq]

/-- A successful arrow lookup returns JSON text or SQL NULL. Substitute the optional node. -/
private theorem arrow_ok (v p) (ok : Returns (arrowSelect v p)) : Returns (arrowJson v p) := by
  obtain ⟨n, eq⟩ := ok
  cases n <;> simp [Returns, arrowJson, eq]

/-- When the inputs satisfy {name}`JsonInputs`, the JSON function returns an SQL value.
Split on the function and its arity. Reuse the same parse, construction and edit proofs
for the corresponding text and binary outputs. -/
theorem jsonSucceeds {f : JsonFunction} {args : List (Value × Bool)} (safe : JsonInputs f args) :
    Succeeds (Json.apply f) args := by
  change Returns (Json.apply f args)
  cases f <;> rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩ <;>
    simp only [Json.apply, JsonInputs, List.map_cons, List.map_nil] at *
  all_goals first
    | exact ⟨_, rfl⟩
    | exact safe
    | exact map_ok _ safe
    | exact selected_ok _ safe
    | exact valid_ok _ _ (by decide)
    | exact valid_ok _ _ safe
    | exact edit_ok _ _ _ safe
    | exact remove_ok _ _ safe
    | exact (extractInputs_iff _ _).mp safe
    | exact binaryExtract_ok safe
    | exact object_ok _ safe
    | exact map_ok _ (object_ok _ safe)
    | exact map_ok _ (map_ok _ safe)
    | exact patch_ok _ _ _ safe
    | obtain ⟨⟨n, eq⟩, get⟩ := safe
      cases n with
      | none => exact ⟨.null, by simp [arrowValue, eq]⟩
      | some n => simpa [arrowValue, eq] using get n eq
    | exact pretty_ok _ _ safe
    | exact position_ok _ safe
    | exact arrow_ok _ _ safe

end Belay.Sqlite.Model.Resolved.CallSafety
