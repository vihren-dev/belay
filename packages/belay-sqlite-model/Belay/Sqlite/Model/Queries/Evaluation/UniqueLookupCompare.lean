import Belay.Sqlite.Model.Queries.Evaluation.UniqueLookupCells

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- For every two values and collation: the comparison {lit}`=` of the two values ({name}`Comparison.apply`) is true
({name}`truthy`) exactly when neither value is NULL and the two values compare as equal under the collation. Proof
sketch: unfold {name}`Comparison.apply` and split on NULL. -/
theorem truthy_eq_apply (left right : Value) (collation : Collation) :
    truthy (Comparison.eq.apply left right collation) = true ↔
      left ≠ .null ∧ right ≠ .null ∧ collation.compare left right = .eq := by
  cases left <;> cases right <;> simp [Comparison.apply, Value.isNull, truth, truthy, Comparison.holds]

end Belay.Sqlite.Model.Resolved
