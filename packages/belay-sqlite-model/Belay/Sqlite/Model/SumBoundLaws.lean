import Belay.Sqlite.Model.SumIntegerLaws
set_option doc.verso true

/-! Sufficient bounds for SUM over mixed numeric cells. INTEGER affinity can retain REAL
values, so the safe-sum laws include them as well as integers and NULLs. -/

namespace Belay.Sqlite.Model

/-- For every approximate state with no overflow flag and every value, adding the value
keeps the state approximate without overflow. Proof sketch: inspect the converted input;
integer and double addition preserve these two flags. -/
theorem SumState.add_approximate_safe (state : SumState) (value : Value)
    (approximate : state.approximate = true) (safe : state.overflow = false) :
    (state.add value).approximate = true ∧ (state.add value).overflow = false := by
  unfold SumState.add
  cases value.sumInput? with
  | none => exact ⟨approximate, safe⟩
  | some input =>
    cases input with
    | integer n =>
      simp only [approximate, SumState.addInteger, SumState.addDouble]
      split <;> simp [safe]
    | double f => simp [approximate, SumState.addDouble]

/-- For every list of values and approximate state without overflow, adding every value
keeps the overflow flag false. Proof sketch: induction using
{name}`SumState.add_approximate_safe`. -/
theorem sumFold_approximate_safe (values : List Value) : ∀ state : SumState,
    state.approximate = true → state.overflow = false →
      (values.foldl SumState.add state).overflow = false := by
  induction values with
  | nil => intro state _ safe; exact safe
  | cons head tail ih =>
    intro state approximate safe
    have next := SumState.add_approximate_safe state head approximate safe
    exact ih _ next.1 next.2

/-- For every list containing only NULLs, integers and reals, and every exact state
without overflow, if each prefix sum of its integer cells added to the starting sum fits
in 64 bits, the final state has no overflow flag. This sufficient condition also bounds
integers after the first real, although they cannot cause integer overflow.
Proof sketch: NULLs leave the state, integers stay exact while their sums fit, and the
first real starts an approximate state that remains safe. -/
theorem sumFold_numeric_safe (values : List Value)
    (numeric : ∀ value ∈ values, value = .null ∨ (∃ n, value = .integer n) ∨ (∃ r, value = .real r)) :
    ∀ state : SumState, state.approximate = false → state.overflow = false →
      (∀ k, fitsInt64Range (state.integerSum + ((integerCells values).take k).sum) = true) →
      (values.foldl SumState.add state).overflow = false := by
  induction values with
  | nil => intro state _ safe _; exact safe
  | cons head tail ih =>
    intro state exact safe fits
    have later : ∀ value ∈ tail, value = .null ∨ (∃ n, value = .integer n) ∨ (∃ r, value = .real r) :=
      fun value member => numeric value (List.mem_cons_of_mem _ member)
    rcases numeric head (List.mem_cons_self ..) with null | ⟨n, integer⟩ | ⟨r, real⟩
    · subst null
      simpa [SumState.add, Value.sumInput?] using ih later state exact safe (by simpa [integerCells] using fits)
    · subst integer
      have first : fitsInt64Range (state.integerSum + n) = true := by simpa [integerCells] using fits 1
      rw [List.foldl_cons, SumState.add_integer_exact state n exact first]
      apply ih later { state with count := state.count + 1, integerSum := state.integerSum + n } exact safe
      intro k
      simpa [integerCells, Int.add_assoc] using fits (k+1)
    · subst real
      apply sumFold_approximate_safe tail (state.add (.real r))
      · simp [SumState.add, Value.sumInput?, exact, SumState.startApproximate, SumState.addDouble]
        split <;> rfl
      · simp [SumState.add, Value.sumInput?, exact, SumState.startApproximate, SumState.addDouble]
        split <;> exact safe

/-- For every list of integers and bound, if each integer is between the negative and
positive bound, their sum is between the negative and positive list length times that
bound. The empty list satisfies the result for any bound. Proof sketch: induction adds
the head bounds to the bounds for the remaining sum. -/
theorem integer_sum_bound (values : List Int) (bound : Int)
    (bounded : ∀ value ∈ values, -bound ≤ value ∧ value ≤ bound) :
    -(values.length : Int) * bound ≤ values.sum ∧ values.sum ≤ (values.length : Int) * bound := by
  induction values with
  | nil => simp
  | cons head tail ih =>
    have headBound := bounded head (by simp)
    have tailBound := ih (fun value member => bounded value (by simp [member]))
    simp only [List.length_cons, List.sum_cons, Int.natCast_add, Int.natCast_one, Int.add_mul,
      Int.one_mul, Int.neg_add, Int.neg_mul] at *
    omega

/-- For every list of NULLs, integers and reals and nonnegative integer bound, if each
integer cell is within that bound and the number of all values times the bound is at
most the largest 64-bit integer, SUM does not give integer overflow. REAL values need no
bound here because approximate summation has no integer overflow error.
Proof sketch: every prefix has at most as many integer cells as the full value list,
so {name}`integer_sum_bound` keeps its sum within 64 bits; {name}`sumFold_numeric_safe`
then leaves no overflow flag. -/
theorem sumOf_no_overflow_of_bound (values : List Value) (bound : Int)
    (nonnegative : 0 ≤ bound)
    (numeric : ∀ value ∈ values, value = .null ∨ (∃ n, value = .integer n) ∨ (∃ r, value = .real r))
    (bounded : ∀ n ∈ integerCells values, -bound ≤ n ∧ n ≤ bound)
    (size : (values.length : Int) * bound ≤ 9223372036854775807) :
    (sumOf values).sumValue.isNone = false := by
  have prefixes : ∀ k, fitsInt64Range (((integerCells values).take k).sum) = true := by
    intro k
    have sumBound := integer_sum_bound ((integerCells values).take k) bound
      (fun n member => bounded n (List.mem_of_mem_take member))
    have lengthBound : (((integerCells values).take k).length : Int) ≤ (values.length : Int) := by
      exact Int.ofNat_le.mpr (Nat.le_trans (by simp only [List.length_take]; exact Nat.min_le_right _ _) (List.length_filterMap_le ..))
    have multBound := Int.mul_le_mul_of_nonneg_right lengthBound nonnegative
    simp only [fitsInt64Range, Bool.and_eq_true, decide_eq_true_eq]
    change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
    simp only [Int.neg_mul] at sumBound
    omega
  have safe := sumFold_numeric_safe values numeric {} rfl rfl (by simpa using prefixes)
  apply Bool.eq_false_iff.mpr
  intro fails
  have overflow := (SumState.sumValue_isNone_iff _).mp fails |>.2.2
  simp only [sumOf] at overflow
  simp [safe] at overflow
end Belay.Sqlite.Model
