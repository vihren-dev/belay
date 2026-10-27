import Belay.Sqlite.Model.InValueEqualsLaws
import Belay.Sqlite.Model.ExprEvalLaws

set_option doc.verso true

/-! The value laws of {lit}`x IN (SELECT c FROM u)` and {lit}`x NOT IN (SELECT c FROM u)` (task 20261027):
{name}`Belay.Sqlite.Model.Resolved.inValue` equals the disjunction of {lit}`x = c` over the candidates, or its NOT
({lit}`inValue_eq_equalsAny`); {lit}`IN` is true exactly when some comparison is true ({lit}`truthy_inValue_eq_any`);
and {lit}`NOT IN` equals the two-valued test of the correlated {lit}`NOT EXISTS`
({lit}`inValue_negated_eq_not_exists`) when {lit}`x` and every candidate are not NULL. -/

namespace Belay.Sqlite.Model.Resolved

/-- For all operands and a collation, the comparison {lit}`a = b` ({name}`Comparison.apply`) is true exactly when
neither operand is NULL and the collation sees them equal. Proof sketch: a NULL operand gives NULL, which is
not true, and else the comparison is 1 or 0 by the collation. -/
theorem truthy_apply_eq (a b : Value) (collation : Collation) :
    truthy (Comparison.eq.apply a b collation) = (!a.isNull && !b.isNull && collation.compare a b == .eq) := by
  unfold Comparison.apply
  cases ha : a.isNull <;> cases hb : b.isNull <;> simp [Comparison.holds, truthy_truth, truthy_null]

/-- For all operands and a collation, the comparison {lit}`a = b` is NULL exactly when an operand is NULL. Proof
sketch: a NULL operand gives NULL, and else the comparison is 1 or 0. -/
theorem isNull_apply_eq (a b : Value) (collation : Collation) :
    (Comparison.eq.apply a b collation).isNull = (a.isNull || b.isNull) := by
  unfold Comparison.apply
  cases ha : a.isNull <;> cases hb : b.isNull <;> simp

/-- For every affinity, collation, probe and candidate, the comparison {lit}`x = c` is true exactly when the
probe is not NULL and the candidate matches ({name}`inMatches`) under the comparison's affinity and
collation. Proof sketch: {name}`comparisonOperands_isNull` shows that the operands are NULL exactly when
the probe or the candidate is; {name}`truthy_apply_eq` then reads the comparison. -/
theorem truthy_equalsValue (affinity : Option Affinity) (collation : Collation) (value candidate : Value) :
    truthy (equalsValue affinity collation value candidate) = (!value.isNull && inMatches affinity collation value candidate) := by
  obtain ⟨left, right⟩ := comparisonOperands_isNull affinity value candidate
  unfold equalsValue compareValue inMatches
  rcases hp : comparisonOperands affinity value candidate with ⟨a, b⟩
  rw [hp] at left right
  simp only [truthy_apply_eq, left, right]
  cases value.isNull <;> simp

/-- For every affinity, collation, probe and candidate, the comparison {lit}`x = c` is NULL exactly when the probe
or the candidate is NULL. Proof sketch: {name}`comparisonOperands_isNull` shows that the operands are NULL
exactly then, and {name}`isNull_apply_eq` reads the comparison. -/
theorem isNull_equalsValue (affinity : Option Affinity) (collation : Collation) (value candidate : Value) :
    (equalsValue affinity collation value candidate).isNull = (value.isNull || candidate.isNull) := by
  obtain ⟨left, right⟩ := comparisonOperands_isNull affinity value candidate
  unfold equalsValue compareValue
  rcases hp : comparisonOperands affinity value candidate with ⟨a, b⟩
  rw [hp] at left right
  simp only [isNull_apply_eq, left, right]

/-- For every value and flags, the disjunction of a value with a result that is 1, NULL or 0 by two flags is 1 when
the value is true or the first flag is set, else NULL when the value is NULL or the second flag is set, else
0. Proof sketch: case analysis on the flags and on whether the value is NULL and true. -/
theorem or_flags (x : Value) (anyTrue anyNull : Bool) :
    x.or (if anyTrue then truth true else if anyNull then .null else truth false) =
      if (truthy x || anyTrue) then truth true else if (x.isNull || anyNull) then .null else truth false := by
  have onNull : x.isNull = true → truthy x = false := Value.truthy_of_isNull
  unfold Value.or
  cases anyTrue <;> cases anyNull <;> cases hx : truthy x <;> cases hn : x.isNull <;> simp_all [truthy_truth, truthy_null]

/-- For every list of candidates, the disjunction {name}`equalsAny` is 1 when some comparison is true, else NULL when
some comparison is NULL, else 0. Proof sketch: induction on the candidates, with {name}`or_flags` for the
step. -/
theorem equalsAny_eq (affinity : Option Affinity) (collation : Collation) (value : Value) (candidates : List Value) :
    equalsAny affinity collation value candidates =
      if candidates.any (fun candidate => truthy (equalsValue affinity collation value candidate)) then truth true
      else if candidates.any (fun candidate => (equalsValue affinity collation value candidate).isNull) then .null
      else truth false := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
    unfold equalsAny at ih ⊢
    simp only [List.foldr_cons, ih, or_flags, List.any_cons]
    rfl

/-- **Value law.** For every affinity and collation of the {lit}`IN` test and of the comparison {lit}`=`, either
polarity, every probe and every list of candidates: if the {lit}`IN` test and the comparison match the same candidates
({name}`inMatches`), then {lit}`x IN (c1, ..., cn)` is the value of {lit}`x = c1 OR ... OR x = cn`
({name}`equalsAny`), and {lit}`x NOT IN (c1, ..., cn)` is the value of its {lit}`NOT`, also when a value is NULL. The two
sides are equal as values: for no candidate both are 0 ({lit}`IN`) or 1 ({lit}`NOT IN`); a NULL probe with a candidate
gives NULL for both; a match gives 1 ({lit}`IN`) or 0 ({lit}`NOT IN`); no match with a NULL candidate gives NULL; and no
match without a NULL candidate gives 0 ({lit}`IN`) or 1 ({lit}`NOT IN`). The agreement is needed only for a probe that is
not NULL, because a NULL probe gives NULL for both. Proof sketch: read both sides by cases ({name}`inValue_cases`,
{name}`equalsAny_eq`) and use {name}`truthy_equalsValue` and {name}`isNull_equalsValue` for the comparisons; each of the
cases gives equal values. -/
theorem inValue_eq_equalsAny (inAffinity : Option Affinity) (inCollation : Collation)
    (equalsAffinity : Option Affinity) (equalsCollation : Collation) (negated : Bool) (value : Value)
    (candidates : List Value)
    (agree : value.isNull = false → ∀ candidate ∈ candidates,
      inMatches inAffinity inCollation value candidate = inMatches equalsAffinity equalsCollation value candidate) :
    inValue inAffinity inCollation negated value candidates =
      if negated then (equalsAny equalsAffinity equalsCollation value candidates).not
      else equalsAny equalsAffinity equalsCollation value candidates := by
  rw [inValue_cases, equalsAny_eq]
  by_cases empty : candidates = []
  · subst empty; cases negated <;> rfl
  · have nonempty : candidates.isEmpty = false := by simpa [List.isEmpty_iff] using empty
    cases hv : value.isNull
    · rw [any_congr_of_mem (agree hv)]
      simp only [truthy_equalsValue, isNull_equalsValue, hv, nonempty, Bool.not_false, Bool.true_and, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte]
      cases negated <;> cases candidates.any (inMatches equalsAffinity equalsCollation value) <;>
        cases candidates.any (·.isNull) <;> simp [Value.not, truthy_truth]
    · obtain ⟨c, member⟩ := List.exists_mem_of_ne_nil _ empty
      have anyNull : candidates.any (fun c => (equalsValue equalsAffinity equalsCollation value c).isNull) = true :=
        List.any_eq_true.mpr ⟨c, member, by simp [isNull_equalsValue, hv]⟩
      have noTruthy : candidates.any (fun c => truthy (equalsValue equalsAffinity equalsCollation value c)) = false := by
        simp only [List.any_eq_false]
        exact fun c _ => by simp [truthy_equalsValue, hv]
      cases negated <;> simp [noTruthy, anyNull, nonempty, Value.not]

/-- **Truth of IN.** For the same affinities and collations, probe and candidates, when the {lit}`IN` test and the
comparison {lit}`=` match the same candidates, {lit}`x IN (c1, ..., cn)` is true exactly when some comparison
{lit}`x = ci` is true. It needs no premise on NULL: a NULL probe or a NULL candidate makes the comparison and the test
not true, and an empty list gives no true comparison. So a {lit}`WHERE` keeps a row for {lit}`IN` against
{lit}`EXISTS` of the comparisons. The values can differ: {lit}`IN` can be NULL where {lit}`EXISTS` is 0. Proof sketch:
{name}`inValue_eq_equalsAny` for the positive polarity, then {name}`equalsAny_eq` is 1 exactly when a comparison is
true. -/
theorem truthy_inValue_eq_any (inAffinity : Option Affinity) (inCollation : Collation)
    (equalsAffinity : Option Affinity) (equalsCollation : Collation) (value : Value) (candidates : List Value)
    (agree : value.isNull = false → ∀ candidate ∈ candidates,
      inMatches inAffinity inCollation value candidate = inMatches equalsAffinity equalsCollation value candidate) :
    truthy (inValue inAffinity inCollation false value candidates) =
      candidates.any (fun candidate => truthy (equalsValue equalsAffinity equalsCollation value candidate)) := by
  rw [inValue_eq_equalsAny inAffinity inCollation equalsAffinity equalsCollation false value candidates agree]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [equalsAny_eq]
  by_cases some : candidates.any (fun candidate => truthy (equalsValue equalsAffinity equalsCollation value candidate))
  · simp [some, truthy_truth]
  · have none_ : candidates.any (fun candidate => truthy (equalsValue equalsAffinity equalsCollation value candidate)) =
        false := by simpa using some
    rw [none_]
    simp only [Bool.false_eq_true, ↓reduceIte]
    split <;> simp [truthy_truth, truthy_null]

/-- **Filter form of the value law.** If the probe is not NULL and no candidate is NULL, and the {lit}`IN` test and the
comparison {lit}`=` match the same candidates ({name}`inMatches`), then {lit}`x NOT IN (c1, ..., cn)` is the value 1 when no
comparison {lit}`x = ci` is true and 0 otherwise: the value of the correlated {lit}`NOT EXISTS` over the candidates. When
the probe is NULL, {lit}`NOT IN` of a non-empty list is NULL and {lit}`NOT EXISTS` is 1. When a candidate is NULL and no
other candidate matches, {lit}`NOT IN` is NULL and {lit}`NOT EXISTS` is 1. Proof sketch: with no NULL, the
branches of {name}`inValue` that give NULL do not apply, and the others give 1 or 0 by whether a candidate matches
({name}`truthy_equalsValue`). -/
theorem inValue_negated_eq_not_exists (inAffinity : Option Affinity) (inCollation : Collation)
    (equalsAffinity : Option Affinity) (equalsCollation : Collation) (value : Value) (candidates : List Value)
    (probe : value.isNull = false) (candidatesKnown : ∀ candidate ∈ candidates, candidate.isNull = false)
    (agree : ∀ candidate ∈ candidates,
      inMatches inAffinity inCollation value candidate = inMatches equalsAffinity equalsCollation value candidate) :
    inValue inAffinity inCollation true value candidates =
      truth (!candidates.any (fun candidate => truthy (equalsValue equalsAffinity equalsCollation value candidate))) := by
  have noNull : candidates.any (·.isNull) = false := by
    simp only [List.any_eq_false]
    exact fun c h => by simp [candidatesKnown c h]
  rw [inValue_cases, any_congr_of_mem agree]
  simp only [truthy_equalsValue, probe, Bool.not_false, Bool.true_and, noNull]
  by_cases empty : candidates = []
  · subst empty; rfl
  · have nonempty : candidates.isEmpty = false := by simpa [List.isEmpty_iff] using empty
    cases candidates.any (inMatches equalsAffinity equalsCollation value) <;> simp [nonempty]

end Belay.Sqlite.Model.Resolved
