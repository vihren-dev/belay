import Belay.Sqlite.Model.Queries.Preparation.ModelLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every test, list and appended item that the test rejects: the search over the longer
list finds what the search over the list finds. Proof sketch: a hit in the list stays
({name}`findPosition_append`); with no hit, the search reaches the rejected item and finds
nothing. -/
theorem findPosition_append_single_rejected {α : Type} {test : α → Bool} (items : List α) {item : α}
    (rejected : test item = false) :
    findPosition test (items ++ [item]) = findPosition test items := by
  induction items with
  | nil => simp [findPosition, rejected]
  | cons head rest ih =>
    by_cases hit : test head = true
    · simp [findPosition, hit]
    · simp only [List.cons_append, findPosition, hit, Bool.false_eq_true, ↓reduceIte, ih]

end Belay.Sqlite.Model
