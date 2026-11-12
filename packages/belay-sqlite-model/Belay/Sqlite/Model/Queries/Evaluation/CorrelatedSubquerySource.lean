import Belay.Sqlite.Model.Queries.Evaluation.ExceptSubqueryRun
import Belay.Sqlite.Model.Queries.Evaluation.InIntegerProbe

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- For every two lists, a position past the first list and a default, the cell of the joined list at the position
shifted by the length of the first list is the cell of the second list at the position. Proof sketch: the
cell is the optional element at the position, which {name}`List.getElem?_append_right` moves. -/
theorem getD_append_length_add {α : Type} (first second : List α) (position : Nat) (default : α) :
    (first ++ second).getD (first.length + position) default = second.getD position default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    ← List.getD_eq_getElem?_getD]

/-- For every two lists, a position inside the first list and a default, the cell of the joined list at the position
is the cell of the first list. Proof sketch: {name}`List.getElem?_append_left`. -/
theorem getD_append_of_lt {α : Type} (first second : List α) {position : Nat} (inside : position < first.length)
    (default : α) : (first ++ second).getD position default = first.getD position default := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left inside, ← List.getD_eq_getElem?_getD]

end Belay.Sqlite.Model.Resolved
