import Belay.Sqlite.Model.Queries.Evaluation.PossibleResultsLemmas

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Normalizing result rows preserves whether the result is empty. Proof sketch: normalization
preserves the row count, and a list is empty exactly when that count is zero. -/
theorem Resolved.normalForm_eq_nil (rows : List (List Value)) :
    Resolved.normalForm rows = [] ↔ rows = [] := by
  rw [← List.length_eq_zero_iff, Resolved.normalForm_length, List.length_eq_zero_iff]

end Belay.Sqlite.Model
