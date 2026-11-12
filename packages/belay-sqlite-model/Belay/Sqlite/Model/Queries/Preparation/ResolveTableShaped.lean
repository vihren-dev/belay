import Belay.Sqlite.Model.Queries.Preparation.Definitions

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every list and function, {name}`updateLast` of the list with the function has the length of the list. Proof sketch: induction over the list; the cases for the empty list and for one element keep the length.  -/
theorem length_updateLast (items : List α) (change : α → α) : (updateLast items change).length = items.length := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    cases rest with
    | nil => rfl
    | cons second more => simp [updateLast, ih]

/-- For every list, function and position with at least one element after it, {name}`updateLast` of the list with the function has at the position the element of the list. Proof sketch: induction over the list; only the last element changes.  -/
theorem getElem?_updateLast (items : List α) (change : α → α) {position : Nat} (inside : position + 1 < items.length) :
    (updateLast items change)[position]? = items[position]? := by
  induction items generalizing position with
  | nil => simp at inside
  | cons first rest ih =>
    cases rest with
    | nil => simp at inside
    | cons second more =>
      cases position with
      | zero => simp [updateLast]
      | succ place => simpa [updateLast] using ih (by simpa using inside)

/-- For every list, function that changes an element, and function on the elements whose value the change keeps, the values of the function on {name}`updateLast` of the list with the change are the values of the function on the list. Proof sketch: induction over the list; only the last element changes, and its value is kept.  -/
theorem map_updateLast (items : List α) (change : α → α) (value : α → β) (keeps : ∀ item, value (change item) = value item) :
    (updateLast items change).map value = items.map value := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    cases rest with
    | nil => simp [updateLast, keeps]
    | cons second more => simpa [updateLast] using ih

end Belay.Sqlite.Model
