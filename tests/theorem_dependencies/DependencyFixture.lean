set_option doc.verso true

/-! Exercise dependency export through source statements, tactic elaboration and generated helpers. -/

namespace DependencyFixture

/-- A named proposition used only in a theorem's statement. -/
def statementPredicate : Prop := True

/-- The named proposition holds; its proof uses the unfolded proposition. -/
theorem statementOnly : statementPredicate := True.intro

/-- A proposition whose proof requires a constructor or the named theorem below. -/
inductive Wrapped (n : Nat) : Prop where
  /-- Each natural number has a witness of the proposition. -/
  | intro : Wrapped n

/-- For every natural number, the wrapped proposition holds. Its constructor supplies the proof. -/
@[simp] theorem unwrap (n : Nat) : Wrapped n := Wrapped.intro

/-- For every natural number, the wrapped proposition holds. Simplification selects {lean}`unwrap`. -/
theorem tacticSelected (n : Nat) : Wrapped n := by simp

/-- A private proof keeps the full kernel name visible in the raw graph. -/
private theorem privateProof : True := True.intro

/-- For every natural number, a recursive local helper returns a proof of true. -/
theorem throughGenerated (n : Nat) : True := by
  let rec loop (m : Nat) : True :=
    match m with
    | 0 => privateProof
    | Nat.succ k => loop k
  exact loop n

/-- The selection follows a non-BMP character, so its UTF-16 column differs from a character count. -/
/- 𝄞 -/ theorem unicodeSelected : True := True.intro

end DependencyFixture
