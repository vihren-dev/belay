import Belay.Sqlite.Model.Shared.Catalog.Database

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every test, list and found position: if {name}`findPosition` finds the
position, it is below the list length. The proof inducts over the list: the
head gives position zero, and a later match adds one to a position that is below
the tail length. -/
theorem findPosition_lt {test : α → Bool} {items : List α} (found : findPosition test items = some (index, item)) :
    index < items.length := by
  induction items generalizing index with
  | nil => simp [findPosition] at found
  | cons head rest ih =>
    simp only [findPosition] at found
    split at found
    · cases found; simp
    · obtain ⟨⟨inner, value⟩, innerFound, equal⟩ := Option.map_eq_some_iff.mp found
      cases equal
      simpa using ih innerFound

/-- For every test, list, suffix and found position: appending a suffix keeps the
position that {name}`findPosition` finds in the list. The proof inducts over the
list: the search stops at the same item before it reaches the suffix. -/
theorem findPosition_append {test : α → Bool} {items : List α} (more : List α)
    (found : findPosition test items = some (index, item)) :
    findPosition test (items ++ more) = some (index, item) := by
  induction items generalizing index with
  | nil => simp [findPosition] at found
  | cons head rest ih =>
    simp only [findPosition, List.cons_append] at found ⊢
    split at found
    · simp_all
    · obtain ⟨⟨inner, value⟩, innerFound, equal⟩ := Option.map_eq_some_iff.mp found
      cases equal
      simp_all

/-- For every requested name, {name}`columnPosition` finds a column of the table.
An empty name list requires nothing; repeated names are allowed. Use this to
establish column presence before projection; row width is separate. -/
def Covers (table : Table) (names : List Identifier) : Prop :=
  ∀ name ∈ names, ∃ index, columnPosition table.shape.columns name = some index

end Belay.Sqlite.Model
