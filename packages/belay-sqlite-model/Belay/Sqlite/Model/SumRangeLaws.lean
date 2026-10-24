import Belay.Sqlite.Model.SumBoundLaws
import Belay.Sqlite.Model.IntegerCompareLaws
import Belay.Sqlite.Model.ExprEvalLaws

set_option doc.verso true

/-! Direct comparisons with integer bounds imply the mixed-value SUM bound. -/

namespace Belay.Sqlite.Model
open Resolved

/-- For every value, pair of integer bounds and collation, if NOT BETWEEN is not true
when comparing the value directly with those bounds, the value is NULL, an integer
between the bounds, or a REAL. This sufficient classification places no bound on the
REAL case. Proof sketch: TEXT and BLOB rank above integers and fail the upper bound;
an integer's two comparisons give its lower and upper bounds; NULL and REAL give the
other two cases. -/
theorem Value.numeric_of_not_between (cell : Value) (low high : Int) (collation : Collation)
    (kept : truthy ((Comparison.ge.apply cell (.integer low) collation).and
      (Comparison.le.apply cell (.integer high) collation)).not = false) :
    cell = .null ∨ (∃ n, cell = .integer n ∧ low ≤ n ∧ n ≤ high) ∨ ∃ r, cell = .real r := by
  cases cell with
  | null => exact .inl rfl
  | real r => exact .inr (.inr ⟨r, rfl⟩)
  | integer n =>
    simp only [Comparison.apply, Value.isNull, Bool.false_or, Bool.false_eq_true, ite_false,
      Collation.compare_integer, Comparison.holds] at kept
    have lower : low ≤ n := by
      apply Classical.byContradiction
      intro bad
      have lt : n < low := by omega
      simp [Int.compare_eq_lt.mpr lt, Value.and, Value.not, falsy] at kept
    have upper : n ≤ high := by
      apply Classical.byContradiction
      intro bad
      have gt : high < n := by omega
      simp [Int.compare_eq_gt.mpr gt, Value.and, Value.not, falsy] at kept
    exact .inr (.inl ⟨n, rfl, lower, upper⟩)
  | text bytes | blob bytes =>
    cases collation <;> change true = false at kept <;> contradiction

/-- For every list of values, nonnegative integer bound and collation, if no value
makes NOT BETWEEN the negative and positive bound true when compared directly, and list
length times the bound is within the positive 64-bit range, SUM does not overflow.
NULLs and REAL values are included. A caller with comparison affinity must first show
that its affinity leaves the compared cells unchanged. Proof sketch:
{name}`Value.numeric_of_not_between` classifies each cell and bounds its integer case.
The resulting hypotheses give {name}`sumOf_no_overflow_of_bound`. -/
theorem sumOf_no_overflow_of_between (values : List Value) (bound : Int) (collation : Collation)
    (nonnegative : 0 ≤ bound)
    (within : ∀ value ∈ values, truthy ((Comparison.ge.apply value (.integer (-bound)) collation).and
      (Comparison.le.apply value (.integer bound) collation)).not = false)
    (size : (values.length : Int) * bound ≤ 9223372036854775807) :
    (sumOf values).sumValue.isNone = false := by
  have cells : ∀ value ∈ values,
      value = .null ∨ (∃ n, value = .integer n ∧ -bound ≤ n ∧ n ≤ bound) ∨ ∃ r, value = .real r := by
    intro value member
    exact Value.numeric_of_not_between value (-bound) bound collation (within value member)
  apply sumOf_no_overflow_of_bound values bound nonnegative
  · intro value member
    rcases cells value member with null | ⟨n, eq, _⟩ | real
    · exact .inl null
    · exact .inr (.inl ⟨n, eq⟩)
    · exact .inr (.inr real)
  · intro n member
    simp only [integerCells, List.mem_filterMap] at member
    obtain ⟨value, valueMember, extracted⟩ := member
    cases value <;> simp only [Option.some.injEq, reduceCtorEq] at extracted
    case integer m =>
      subst extracted
      simpa using cells (.integer m) valueMember
  · exact size
end Belay.Sqlite.Model
