import Belay.Sqlite.Model.Queries.Evaluation.ScalarCallSafety
import Belay.Sqlite.Model.Queries.Evaluation.JsonCallSafety

/-! Client proofs over evaluated arguments. These imports need no DELETE or statement context. -/

namespace FunctionCallSafetyCases
open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved Belay.Sqlite.Model.Resolved.CallSafety

/-- Even an unknown list of arguments is safe for a total scalar function. -/
private theorem total (args : List Value) : Succeeds ScalarFunction.length.apply args :=
  ScalarFunction.apply_ok _ _ rfl

/-- LIKE with ESCAPE uses both the pattern length and the UTF-8 character count. -/
private theorem likeEscape (p s esc : Value) (size : p.textBytes.length ≤ likePatternLimit)
    (one : ValidEscape esc) : Succeeds ScalarFunction.like.apply [p, s, esc] :=
  scalarSucceeds ⟨Nat.not_lt.mpr size, one⟩

/-- GLOB uses the same length limit without an escape argument. -/
private theorem glob (p s : Value) (size : p.textBytes.length ≤ likePatternLimit) :
    Succeeds ScalarFunction.glob.apply [p, s] := scalarSucceeds (Nat.not_lt.mpr size)

/-- A successful decoder result is sufficient for Unicode unescaping. -/
private theorem unicode (v out : Value) (decoded : unistrValue v = some out) :
    Succeeds ScalarFunction.unistr.apply [v] := scalarSucceeds ⟨out, decoded⟩

/-- A caller can prove a partial format safe using the format interpreter. -/
private theorem format (fmt : Value) (args : List Value)
    (render : ∀ bytes, cText? fmt = some bytes →
      ∃ out, printfFrom bytes.toArray (bytes.length + 1) 0 args = .ok out) :
    Succeeds ScalarFunction.printf.apply (fmt :: args) := scalarSucceeds render

/-- Default validation accepts any SQL value, even malformed text, with any subtype flag. -/
private theorem valid (v : Value) (tag : Bool) : Succeeds (Json.apply .valid) [(v, tag)] :=
  jsonSucceeds True.intro

/-- Binary extraction uses the same path evidence as text extraction for any path count. -/
private theorem binaryPaths (v : Value) (tag : Bool) (paths : List (Value × Bool))
    (found : Returns (Json.extract v (paths.map Prod.fst))) :
    Succeeds (Json.apply .jsonbExtract) ((v, tag) :: paths) :=
  jsonSucceeds ((extractInputs_iff _ _).mpr found)

/-- Object members carry their own subtype flags into both output encodings. -/
private theorem binaryObject (args : List (Value × Bool)) (even : args.length % 2 ≠ 1)
    (members : Returns (Json.objectMembers args)) : Succeeds (Json.apply .jsonbObject) args := by
  apply jsonSucceeds
  cases args <;> exact ⟨even, members⟩

-- Invalid escape length, flags, and object labels are actual failure boundaries.
example : ScalarFunction.like.apply [.text [97], .text [97], .text [97, 98]] = .error .error := rfl
example : Json.apply .valid [(.null, false), (.integer 0, false)] = .error .badFlags := rfl
example : Json.apply .jsonbObject [(.integer 1, false), (.null, false)] = .error .labelNotText := rfl

#print axioms total
#print axioms likeEscape
#print axioms glob
#print axioms unicode
#print axioms format
#print axioms valid
#print axioms binaryPaths
#print axioms binaryObject
end FunctionCallSafetyCases
