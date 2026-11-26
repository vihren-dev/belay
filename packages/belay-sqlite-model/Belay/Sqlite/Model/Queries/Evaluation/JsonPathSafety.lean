import Belay.Sqlite.Model.Queries.Evaluation.CallSafety

set_option doc.verso true

/-! Safety of JSON paths and of the data operations shared by text and binary functions. -/

namespace Belay.Sqlite.Model.Resolved.CallSafety
open Json

/-- The JSON operation returns a result of its own type, which may include a missing path. -/
def Returns (result : Except JsonError α) : Prop := ∃ out, result = .ok out

/-- The input parses and the operation succeeds on its root if there is one.
A SQL NULL input has no root. -/
def RootReady (v : Value) (next : JsonNode → Prop) : Prop :=
  Returns (parseJsonArgument v) ∧ ∀ root, parseJsonArgument v = .ok (some root) → next root

/-- The edit has its initial document and complete path/value pairs. Its document parses
and applying the edits to a present root succeeds. The zero-argument evaluator returns NULL. -/
def EditInputs (mode : EditMode) : List (Value × Bool) → Prop
  | [] => True
  | (v, _) :: rest => (rest.length + 1) % 2 ≠ 0 ∧ RootReady v (fun root => Returns (applyEdits mode root rest))

/-- The document parses and each removal on its root succeeds. With no arguments the model returns NULL. -/
def RemoveInputs : List Value → Prop
  | [] => True
  | v :: paths => RootReady v (fun root => Returns (applyRemovals root paths))

/-- Mapping a successful result returns the mapped value. Substitute its witness. -/
theorem map_ok (fn : α → β) {result : Except JsonError α} (h : Returns result) :
    Returns (result.map fn) := by obtain ⟨v, eq⟩ := h; exact ⟨fn v, eq ▸ rfl⟩

/-- For a single path the document must parse, lookup must succeed when the path has text,
and a found node must convert to an SQL value. Several paths use the array extractor on the
parsed root. NULLs and missing paths are successful SQL results. -/
def ExtractInputs (v : Value) : List Value → Prop
  | [] => True
  | [p] => RootReady v fun n => ∀ bytes, valueText p = some bytes →
      Returns (lookupFullPath n bytes) ∧
      ∀ found, lookupFullPath n bytes = .ok (some found) → Returns (sqlValueOfNode found)
  | p :: q :: ps => RootReady v fun n => Returns (extractSeveral n (p :: q :: ps) [])

/-- The input conditions hold exactly when text extraction returns a value. Reduce both
sides along the parse, path conversion and lookup results. -/
theorem extractInputs_iff (v : Value) (paths : List Value) :
    ExtractInputs v paths ↔ Returns (extract v paths) := by
  rcases paths with _ | ⟨p, _ | ⟨q, ps⟩⟩
  · simp [ExtractInputs, Returns, extract]
  · unfold ExtractInputs RootReady extract Returns
    cases eq : parseJsonArgument v with
    | error => simp
    | ok n =>
      cases n with
      | none => simp
      | some root =>
        cases h : valueText p with
        | none => simp [h]
        | some bytes =>
          cases found : lookupFullPath root bytes with
          | error => simp [h, found]
          | ok result => cases result <;> simp [h, found]
  · unfold ExtractInputs RootReady extract Returns
    cases eq : parseJsonArgument v with
    | error => simp
    | ok n => cases n <;> simp

/-- Binary extraction returns a value on the same safe inputs as text extraction.
For one path only the rendering of a found container differs. For several paths the
binary function maps the text result to JSONB. -/
theorem binaryExtract_ok {v paths} (h : ExtractInputs v paths) : Returns (jsonbExtract v paths) := by
  rcases paths with _ | ⟨p, _ | ⟨q, ps⟩⟩
  · exact ⟨_, rfl⟩
  · obtain ⟨⟨n, eq⟩, path⟩ := h
    unfold jsonbExtract
    rw [eq]
    cases n with
    | none => exact ⟨_, rfl⟩
    | some root =>
      cases hp : valueText p with
      | none => simp [Returns, hp]
      | some bytes =>
        obtain ⟨⟨node, found⟩, ok⟩ := path root eq bytes hp
        simp only [hp, found]
        cases node with
        | none => exact ⟨_, rfl⟩
        | some n => cases n <;> first | exact ⟨_, rfl⟩ | exact ok _ found
  · exact map_ok _ ((extractInputs_iff _ _).mp h)

end Belay.Sqlite.Model.Resolved.CallSafety
