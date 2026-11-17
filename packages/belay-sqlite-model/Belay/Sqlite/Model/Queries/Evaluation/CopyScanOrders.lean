import Belay.Sqlite.Model.Queries.Evaluation.SourceScanOrders
import Belay.Sqlite.Model.Queries.Evaluation.QueryLaws

set_option doc.verso true

/-! Every scan that SQLite can choose on a table with distinct rowids, including a
partial-index scan, gives exactly the rows of the table in some order. -/

namespace Belay.Sqlite.Model

/-- In a list with distinct rowids, a rowid identifies its row. Proof sketch:
equal rowids occur at the same list position by uniqueness of the mapped list. -/
private theorem eq_of_same_rowid {rows : List Row} (unique : (rows.map Row.rowid).Nodup)
    {a b : Row} (ha : a ∈ rows) (hb : b ∈ rows) (same : a.rowid = b.rowid) : a = b := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
  have inside := (List.getElem?_eq_some_iff.mp hi).1
  have index := unique.eq_of_getElem?_eq (by simpa using inside)
    (show (rows.map Row.rowid)[i]? = (rows.map Row.rowid)[j]? by simp [List.getElem?_map, hi, hj, same])
  subst j
  exact Option.some.inj (hi.symm.trans hj)

/-- For every list of rows with distinct rowids, every list of index keys and every
optional filter, {name}`Table.indexOrder` is a permutation of the input ({name}`List.Perm`),
so it contains exactly the input rows, each once.
Proof sketch: the sort permutes the rows selected by the filter. The remaining
rows are exactly its complement, since a selected rowid identifies a unique row. -/
theorem Table.indexOrder_perm (rows : List Row) (keys : List IndexKey) (filter : Option Resolved.Expr)
    (unique : (rows.map Row.rowid).Nodup) : (Table.indexOrder rows keys filter).Perm rows := by
  let keep := fun row : Row => filter.all fun c => Resolved.truthy (c.eval (Resolved.EvalContext.plain 0) row.values)
  have held (row : Row) (m : row ∈ rows) : (rows.filter keep).any (·.rowid == row.rowid) = keep row := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨other, ⟨member, kept⟩, idEq⟩
      rwa [← eq_of_same_rowid unique member m idEq]
    · exact fun kept => ⟨row, ⟨m, kept⟩, rfl⟩
  unfold Table.indexOrder
  change (_ ++ rows.filter (fun row => !(rows.filter keep).any (·.rowid == row.rowid))).Perm rows
  rw [List.filter_congr (p := fun row => !(rows.filter keep).any (·.rowid == row.rowid))
    (q := fun row => !keep row) (fun row m => congrArg Bool.not (held row m))]
  exact ((Resolved.stableSort_perm _ _).append_right _).trans (List.filter_append_perm keep rows)

/-- For every {name}`Catalog`, position and table with distinct rowids, each member
of {name}`Table.accessOrders` is a permutation of the table’s rows ({name}`List.Perm`). Proof
sketch: the scan has this property and each catalog index permutes the scan.
Discarding duplicate orders only removes members from the list of choices. -/
theorem Table.accessOrders_perm (catalog : Catalog) (position : Nat) (table : Table)
    (unique : (table.rows.map Row.rowid).Nodup) : ∀ order ∈ Table.accessOrders catalog position table,
    order.Perm table.rows := by
  unfold Table.accessOrders
  refine List.foldlRecOn (motive := fun (found : List (List Row)) => ∀ order ∈ found, order.Perm table.rows)
    _ _ (b := []) ?_ ?_
  · simp
  · intro found ih order member
    have perm : order.Perm table.rows := by
      rcases List.mem_cons.mp member with rfl | other
      · exact table.scanRows_perm
      · obtain ⟨⟨keys, filter⟩, _, rfl⟩ := List.mem_map.mp other
        exact (Table.indexOrder_perm _ keys filter
          ((table.scanRows_perm.map Row.rowid).nodup_iff.mpr unique)).trans table.scanRows_perm
    split
    · exact ih
    · simpa [List.mem_append] using fun o (m : o ∈ found ∨ o = order) => m.elim (ih o) (fun eq => eq ▸ perm)

end Belay.Sqlite.Model
