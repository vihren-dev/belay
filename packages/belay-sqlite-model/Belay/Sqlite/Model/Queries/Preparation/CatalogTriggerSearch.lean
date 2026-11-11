import Belay.Sqlite.Model.Queries.Preparation.ModelProjectionLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every test, list and item: if the test finds no element of the list and rejects the item,
it finds no element of the list with the item appended. In plain words, appending a rejected item
cannot create a match. Proof sketch: induction on the list; the head is rejected, as is the appended
item. -/
theorem findPosition_append_rejected {α : Type} {test : α → Bool} {items : List α} {item : α}
    (absent : findPosition test items = none) (rejected : test item = false) :
    findPosition test (items ++ [item]) = none := by
  induction items with
  | nil => simp [findPosition, rejected]
  | cons head rest ih =>
    by_cases hit : test head = true
    · simp [findPosition, hit] at absent
    · have restAbsent : findPosition test rest = none := by simpa [findPosition, hit] using absent
      simpa [findPosition, hit] using ih restAbsent

end Belay.Sqlite.Model
