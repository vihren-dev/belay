import Belay.Sqlite.Model.Queries.Preparation.ColumnSpec
import Belay.Sqlite.Model.Shared.Catalog.CatalogDrop

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every test and list, {name}`findPosition` finds nothing exactly when every
element fails the test. Proof sketch: induction on the list; a passing head is found
at position zero, and a failing head leaves the search to the tail. -/
theorem findPosition_eq_none_iff (test : α → Bool) (items : List α) :
    findPosition test items = none ↔ ∀ item ∈ items, test item = false := by
  induction items with
  | nil => simp [findPosition]
  | cons head rest ih =>
    by_cases passes : test head = true
    · simp [findPosition, passes]
    · simp [findPosition, passes, ih]

end Belay.Sqlite.Model
