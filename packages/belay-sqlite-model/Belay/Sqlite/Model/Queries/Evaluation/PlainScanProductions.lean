import Belay.Sqlite.Model.Queries.Evaluation.InsertSelectSource
import Belay.Sqlite.Model.Queries.Evaluation.PlainQueryRules

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every table and catalog whose access keys all give the rows of the table in the order of its scan
(comparing the rowids), the table has one access order, the scan ({name}`Table.accessOrders`). For example, a
table with no index and no key besides its scan has the one order. Proof sketch: the fold of
{name}`Table.accessOrders` keeps the list with the scan alone whenever the next order has the rowids of the
scan. -/
theorem Table.accessOrders_single (catalog : Catalog) (position : Nat) (table : Table)
    (same : ∀ access ∈ catalog.accessKeys position table.shape,
      (Table.indexOrder table.scanRows access.1 access.2).map Row.rowid = table.scanRows.map Row.rowid) :
    Table.accessOrders catalog position table = [table.scanRows] := by
  unfold Table.accessOrders
  simp only [List.foldl_cons]
  have step : ∀ (orders : List (List Row)), (∀ order ∈ orders, order.map Row.rowid = table.scanRows.map Row.rowid) →
      orders.foldl (fun found order => if found.any (fun other => other.map (·.rowid) == order.map (·.rowid)) then found
        else found ++ [order]) [table.scanRows] = [table.scanRows] := by
    intro orders
    induction orders with
    | nil => intro _; rfl
    | cons order rest ih =>
      intro every
      simp only [List.foldl_cons, List.any_cons, List.any_nil, Bool.or_false]
      rw [every order (List.mem_cons_self ..)]
      simp only [beq_self_eq_true, ite_true]
      exact ih fun other member => every other (List.mem_cons_of_mem _ member)
  have rowids : ∀ order ∈ (catalog.accessKeys position table.shape).map
      fun (keys, filter) => Table.indexOrder table.scanRows keys filter, order.map Row.rowid = table.scanRows.map Row.rowid := by
    intro order member
    obtain ⟨access, accessMember, rfl⟩ := List.mem_map.mp member
    exact same access accessMember
  simp only [List.any_nil, Bool.false_eq_true, ite_false, List.nil_append]
  exact step _ rowids

end Belay.Sqlite.Model
