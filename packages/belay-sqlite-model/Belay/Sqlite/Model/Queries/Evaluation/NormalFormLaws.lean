import Belay.Sqlite.Model.Queries.Evaluation.SelectWindowRules

set_option doc.verso true
set_option exponentiation.threshold 2048

namespace Belay.Sqlite.Model.Resolved

/-- Among equal SQL values the real bit pattern distinguishes every representation.
The absence of a bit pattern sorts before a real. -/
private def realBits : Value → Option UInt64
  | .real bits => some bits
  | _ => none

/-- The normal comparator orders SQL values first and the real representation second.
Values of different storage ranks are already ordered before the tie-break. -/
private theorem compareNormal_lex :
    compareNormal = compareLex Value.compare (compareOn realBits) := by
  funext a b
  cases a <;> cases b <;> first | rfl | simp only [compareNormal, compareLex, compareOn, realBits, Value.compare, Value.rank]
  all_goals first | rfl | (generalize (realScaled _).isSome = numeric; cases numeric <;> rfl)

private instance : Std.TransCmp compareNormal := compareNormal_lex ▸ inferInstance

/-- All values compare equal in normal order exactly when they are identical model values.
Proof sketch: equality gives equal SQL ranks, scaled numbers and bytes. The tie-break recovers the
exact real bits. Equal scaled integers have equal integer values. -/
theorem compareNormal_eq_iff (first second : Value) : compareNormal first second = .eq ↔ first = second := by
  constructor
  · rw [compareNormal_lex]
    simp only [Value.compare, compareLex_eq_eq, compareOn, Std.LawfulEqCmp.compare_eq_iff_eq]
    rintro ⟨⟨rank, number, bytes⟩, bits⟩
    cases first <;> cases second <;> simp_all [Value.rank, Value.scaled, Value.bytes, realBits] <;> omega
  · rintro rfl
    exact Std.ReflCmp.compare_self

private instance : Std.LawfulEqCmp compareNormal where
  eq_of_compare := (compareNormal_eq_iff _ _).mp

/-- Row comparison is the list lexicographic comparator on normal values. -/
private theorem compareRows_lex : compareRows = List.compareLex compareNormal := by
  funext xs ys
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih => cases ys <;> first | rfl | simp [compareRows, ih, List.compareLex_cons_cons]

/-- Two rows compare equal exactly when all their values agree in order, including their lengths.
Proof sketch: lexicographic list comparison has lawful equality because normal value comparison does. -/
theorem compareRows_eq_iff (first second : List Value) : compareRows first second = .eq ↔ first = second := by
  rw [compareRows_lex]
  exact Std.LawfulEqCmp.compare_eq_iff_eq

/-- For a total, transitive and antisymmetric Boolean order, permuting the input gives the same
stable sort. Proof sketch: the two sorted results are ordered permutations of one another. -/
theorem stableSort_eq_of_perm {α : Type} (le : α → α → Bool)
    (total : ∀ a b, le a b || le b a) (trans : ∀ a b c, le a b → le b c → le a c)
    (antisymm : ∀ a b, le a b → le b a → a = b) {first second : List α} (same : first.Perm second) :
    stableSort le first = stableSort le second :=
  List.Perm.eq_of_pairwise (fun a b _ _ => antisymm a b) (stableSort_sorted le trans total first)
    (stableSort_sorted le trans total second) (((stableSort_perm le first).trans same).trans (stableSort_perm le second).symm)

/-- Two lists of rows have the same normal form exactly when one permutes the other.
Proof sketch: sorting permutes each input. Conversely, the normal row comparator is a total
lexicographic order with lawful equality, so sorted permutations coincide. -/
theorem normalForm_eq_iff_perm (first second : List (List Value)) :
    normalForm first = normalForm second ↔ first.Perm second := by
  constructor
  · intro same
    exact (normalForm_perm first).symm.trans (same ▸ normalForm_perm second)
  · intro same
    unfold normalForm
    rw [compareRows_lex]
    apply stableSort_eq_of_perm _ _ _ _ same
    · intro a b
      rw [Std.OrientedCmp.eq_swap (cmp := List.compareLex compareNormal) (a := b)]
      cases List.compareLex compareNormal a b <;> rfl
    · exact fun _ _ _ => Std.TransCmp.isLE_trans
    · intro a b ab ba
      apply Std.LawfulEqCmp.eq_of_compare (cmp := List.compareLex compareNormal)
      apply Ordering.eq_eq_of_isLE_of_isLE_swap ab
      rwa [← Std.OrientedCmp.eq_swap]

end Belay.Sqlite.Model.Resolved
