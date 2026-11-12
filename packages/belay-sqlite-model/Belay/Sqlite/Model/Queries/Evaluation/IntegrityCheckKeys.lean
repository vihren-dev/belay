import Belay.Sqlite.Model.Queries.Evaluation.Comparison

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every collation and two integers, the integers compare as equal under the collation
only when they are equal.
Proof sketch: a collation keeps an integer, and two integers of the same rank compare by their
scaled values, which are equal only for equal integers. -/
theorem Collation.compare_integer_eq (collation : Collation) (first second : Int)
    (equal : collation.compare (.integer first) (.integer second) = .eq) : first = second := by
  have key : ∀ value : Int, collation.key (.integer value) = .integer value := by
    intro value
    cases collation <;> rfl
  simp only [Collation.compare, key, Value.compare, compareLex, compareOn, Value.rank, Value.scaled, Value.bytes,
    Ordering.then_eq_eq, Int.compare_eq_eq] at equal
  exact Int.eq_of_mul_eq_mul_right (Int.ne_of_gt (Int.pow_pos (by decide))) equal.2.1

end Belay.Sqlite.Model
