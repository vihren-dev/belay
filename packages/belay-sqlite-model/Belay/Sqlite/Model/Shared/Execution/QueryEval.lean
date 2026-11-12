import Belay.Sqlite.Model.Shared.Execution.Comparison

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- Insert an item into a list after every leading item that is at most the new
item by {lit}`le`. In a sorted list, the item goes after its equals, which keeps a
sort stable. -/
def insertStable (le : α → α → Bool) (item : α) : List α → List α
  | [] => [item]
  | head :: tail => if le head item then head :: insertStable le item tail else item :: head :: tail

/-- A stable sort by {lit}`le`: each item, in list order, is inserted after its
equals. Unlike {lit}`List.mergeSort`, it uses only structural recursion, so the
kernel can evaluate it in the proofs of conformance cases. -/
def stableSort (le : α → α → Bool) (items : List α) : List α :=
  items.foldl (fun sorted item => insertStable le item sorted) []

end Belay.Sqlite.Model.Resolved
