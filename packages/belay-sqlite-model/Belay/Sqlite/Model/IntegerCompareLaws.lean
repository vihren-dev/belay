import Belay.Sqlite.Model.Comparison

set_option doc.verso true

/-! The comparison of two integers (ADR 0017, S4): under every collation it is the order of the integers, so
a comparison of two integers is the comparison of Lean's integers. -/

namespace Belay.Sqlite.Model

/-- For every positive integer, multiplying two integers by it keeps their order. Proof sketch: the three cases of
the order of the integers; a product with a positive number keeps a strict order and an equality. -/
theorem Int.compare_mul_positive (first second scale : Int) (positive : 0 < scale) :
    Ord.compare (first * scale) (second * scale) = Ord.compare first second := by
  rcases Int.lt_trichotomy first second with less | equal | greater
  · rw [Int.compare_eq_lt.2 less, Int.compare_eq_lt.2 (Int.mul_lt_mul_of_pos_right less positive)]
  · rw [equal, Int.compare_eq_eq.2 rfl, Int.compare_eq_eq.2 rfl]
  · rw [Int.compare_eq_gt.2 greater, Int.compare_eq_gt.2 (Int.mul_lt_mul_of_pos_right greater positive)]

/-- For every collation and two integers, the comparison of the integers under the collation is the order of the
integers. Proof sketch: a collation keeps an integer, and two integers of the same rank compare by their scaled
values, which are the integers times the same positive number ({name}`Int.compare_mul_positive`). -/
theorem Collation.compare_integer (collation : Collation) (first second : Int) :
    collation.compare (.integer first) (.integer second) = Ord.compare first second := by
  have key : ∀ value : Int, collation.key (.integer value) = .integer value := by
    intro value
    cases collation <;> rfl
  have positive : (0 : Int) < 2 ^ 1074 := Int.pow_pos (by decide)
  simp only [Collation.compare, key, Value.compare, compareLex, compareOn, Value.rank, Value.scaled, Value.bytes,
    Int.compare_mul_positive _ _ _ positive]
  cases Ord.compare first second <;> rfl

/-- For every two integers, their order is greater, as a Boolean test, exactly when the second is less
than the first. Proof sketch: a Boolean equation is an equivalence of the two tests, and
{name}`Int.compare_eq_gt` gives it. -/
theorem Int.compare_beq_gt (first second : Int) : (compare first second == Ordering.gt) = decide (second < first) := by
  rw [Bool.eq_iff_iff]
  simp [Int.compare_eq_gt]

/-- For every two natural numbers, the integer literal of the first is less than the integer of the
second exactly when the first is less than the second. Lean writes a numeral such as {lit}`(1 : Int)` as
a literal, not as the integer of a natural number, so the law of the integers of two natural numbers
does not rewrite it. Proof sketch: the literal is by definition the integer of the natural number,
and {lit}`omega` decides the equivalence of the two orders. -/
theorem Int.ofNat_literal_lt_natCast (literal number : Nat) :
    ((no_index (OfNat.ofNat literal) : Int) < (number : Int)) ↔ literal < number := by
  change ((literal : Int) < number) ↔ literal < number
  omega

end Belay.Sqlite.Model
