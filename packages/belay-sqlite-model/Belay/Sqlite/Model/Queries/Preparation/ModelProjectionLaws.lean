import Belay.Sqlite.Model.Queries.Preparation.ModelLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every test, list and item: if {name}`findPosition` finds nothing in the
list and the test accepts the item, it finds the item after the list. The proof
inducts over the list: the test rejects each head, so each step adds one to the
position, and the empty prefix finds the item at position zero. -/
theorem findPosition_append_none {test : α → Bool} {items : List α} (absent : findPosition test items = none)
    (accepted : test item = true) : findPosition test (items ++ [item]) = some (items.length, item) := by
  induction items with
  | nil => simp [findPosition, accepted]
  | cons head rest ih =>
    simp only [findPosition] at absent
    split at absent
    · cases absent
    · rename_i rejected
      have tail := ih (by simpa using absent)
      simp [findPosition, List.cons_append, rejected, tail]

/-- For every table and name list, {name}`Covers` implies that
{name}`columnPosition` finds every requested name. An empty list satisfies both
conditions vacuously. Use it where code checks the lookup of each name. The
proof turns each successful lookup into its Boolean test. -/
theorem Covers.columnsPresent (covered : Covers table names) :
    names.all (fun name => (columnPosition table.shape.columns name).isSome) = true := by
  apply List.all_eq_true.mpr
  intro name member
  obtain ⟨index, found⟩ := covered name member
  simp [found]

end Belay.Sqlite.Model
