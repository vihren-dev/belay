import Belay.Sqlite.Model.Queries.Evaluation.CallSafety

set_option doc.verso true

/-! Input conditions for SQLite scalar calls in any expression. -/

namespace Belay.Sqlite.Model.Resolved.CallSafety

/-- An escape passes the LIKE check if its text, when present, has one UTF-8 leading byte. -/
def ValidEscape (v : Value) : Prop :=
  ∀ bytes, cText? v = some bytes → (bytes.filter fun byte => byte &&& 0xC0 != 0x80).length = 1

/-- Conditions on the evaluated arguments for each scalar call that can fail. Total functions
accept every list. At an arity handled by the evaluator's NULL default there is no obligation.
For printf the format interpreter must finish for the actual format bytes and remaining arguments. -/
def ScalarInputs : ScalarFunction → List Value → Prop
  | .abs, [v] => v ≠ .integer (-(2^63))
  | .zeroblob, [v] => ¬ zeroblobLimit < (if v.toInt64 < 0 then 0 else v.toInt64)
  | .like, [p, _] | .glob, [p, _] => ¬ likePatternLimit < p.textBytes.length
  | .like, [p, _, esc] => (¬ likePatternLimit < p.textBytes.length) ∧ ValidEscape esc
  | .unistr, [v] => ∃ out, unistrValue v = some out
  | .printf, fmt :: rest =>
    ∀ bytes, cText? fmt = some bytes → ∃ out, printfFrom bytes.toArray (bytes.length + 1) 0 rest = .ok out
  | _, _ => True

/-- A pattern within the size limit returns a value when each supplied escape satisfies
{name}`ValidEscape`. Split on the optional escape and its text, then substitute its length. -/
private theorem pattern_ok (dialect : PatternDialect) (p s : Value) (escape : Option Value)
    (size : ¬ likePatternLimit < p.textBytes.length)
    (valid : ∀ v ∈ escape, ValidEscape v) :
    ∃ value, likeResult dialect p s escape = .ok value := by
  unfold likeResult
  simp only [size, ↓reduceIte]
  cases escape with
  | none => exact ⟨_, rfl⟩
  | some v =>
    cases h : cText? v with
    | none => simp [h, Except.map]
    | some bytes =>
      simp [h, valid v rfl bytes h, Except.map]

/-- ABS can return a value when its argument differs from the smallest signed integer.
Proof sketch: inspect the storage class and exclude the overflowing integer. -/
theorem absSucceeds (v : Value) (safe : v ≠ .integer (-(2^63))) :
    Succeeds ScalarFunction.abs.apply [v] := by
  cases v <;> try exact ⟨_, rfl⟩
  rename_i n
  have bound : n ≠ -9223372036854775808 := fun eq => safe (congrArg Value.integer eq)
  simp [Succeeds, ScalarFunction.apply, bound]

/-- A zeroblob of the requested nonnegative size succeeds within the model limit.
Rewrite the evaluator's size check with the supplied bound. -/
theorem zeroblobSucceeds (v : Value)
    (fits : ¬ zeroblobLimit < (if v.toInt64 < 0 then 0 else v.toInt64)) :
    Succeeds ScalarFunction.zeroblob.apply [v] := by
  simp [Succeeds, ScalarFunction.apply, fits]

/-- If decoding the Unicode escapes gives a value, UNISTR returns that value.
Substitute the decoder's result in the scalar evaluator. -/
private theorem unistr_ok (v : Value) (h : ∃ out, unistrValue v = some out) :
    Succeeds ScalarFunction.unistr.apply [v] := by
  obtain ⟨out, ok⟩ := h
  exact ⟨out, by simp [ScalarFunction.apply, ok]⟩

/-- If the format interpreter succeeds on the bytes of the format, printf returns a value.
A NULL format returns NULL directly. Otherwise map the successful bytes to SQL text. -/
private theorem printf_ok (fmt : Value) (rest : List Value) (h : ScalarInputs .printf (fmt :: rest)) :
    Succeeds ScalarFunction.printf.apply (fmt :: rest) := by
  cases eq : cText? fmt with
  | none => exact ⟨.null, by simp [ScalarFunction.apply, printfValue, eq]⟩
  | some bytes =>
    obtain ⟨out, ok⟩ := h bytes eq
    exact ⟨.text out, by simp [ScalarFunction.apply, printfValue, eq, ok, Except.map]⟩

/-- If the inputs satisfy {name}`ScalarInputs`, the scalar evaluator returns a SQL value.
Use {name}`ScalarFunction.apply_ok` for total functions. For the six partial functions,
split on arity and use the input condition at the evaluator's error branch. -/
theorem scalarSucceeds {f : ScalarFunction} {args : List Value} (safe : ScalarInputs f args) :
    Succeeds f.apply args := by
  by_cases total : f.canFail = false
  · exact f.apply_ok args total
  cases f <;> simp [ScalarFunction.canFail] at total
  all_goals
    cases args with
    | nil => exact ⟨_, rfl⟩
    | cons a tail =>
      first
      | exact printf_ok a tail safe
      | cases tail with
        | nil => first | exact ⟨_, rfl⟩ | exact absSucceeds _ safe | exact zeroblobSucceeds _ safe | exact unistr_ok _ safe
        | cons b tail =>
          cases tail with
          | nil => first | exact ⟨_, rfl⟩ | exact pattern_ok _ a b none safe (by simp)
          | cons e tail =>
            cases tail with
            | nil => first | exact ⟨_, rfl⟩ | exact pattern_ok _ a b (some e) safe.1 (by simpa using safe.2)
            | cons => exact ⟨_, rfl⟩

end Belay.Sqlite.Model.Resolved.CallSafety
