import Belay.Sqlite.Model.ForeignKeyComparison
import Belay.Sqlite.Model.ForeignKeySatisfied
import Belay.Sqlite.Model.DatabaseLaws

set_option doc.verso true

/-! A deleted parent can invalidate a lookup only through a matching child scan, under the explicit comparison premise. -/

namespace Belay.Sqlite.Model

/-- For every parent lookup without a skipped row, finding a parent in a list is exactly
finding it in at least one singleton list. This splits a lookup across a physical deletion.
Proof sketch: both rowid and column lookups use the same list existential. -/
theorem parentFound_any (parent : CatalogTable) (key : ParentKey) (link : ForeignKeyLink)
    (values : List Value) (rows : List Row) :
    parentFound parent key link values rows none =
      rows.any (fun row => parentFound parent key link values [row] none) := by
  cases key with
  | rowid =>
    simp only [parentFound]
    split <;> simp
  | columns pairs => simp [parentFound]

/-- For every successful parent lookup, removing all rows with the old rowid either leaves
a successful lookup or the old row alone satisfies it. The identity premise says every row
with that rowid equals the old row. Proof sketch: the original witness is kept or removed. -/
theorem parentFound_remove_split (parent : CatalogTable) (key : ParentKey) (link : ForeignKeyLink)
    (values : List Value) (rows : List Row) (old : Row)
    (identity : ∀ candidate ∈ rows, candidate.rowid = old.rowid → candidate = old)
    (found : parentFound parent key link values rows none = true) :
    parentFound parent key link values (rows.filter (·.rowid != old.rowid)) none = true ∨
      parentFound parent key link values [old] none = true := by
  rw [parentFound_any] at found
  obtain ⟨candidate, member, foundParent⟩ := List.any_eq_true.mp found
  by_cases same : candidate.rowid = old.rowid
  · exact .inr (identity candidate member same ▸ foundParent)
  · apply Or.inl
    rw [parentFound_any]
    exact List.any_eq_true.mpr ⟨candidate, List.mem_filter.mpr ⟨member, by simp [same]⟩, foundParent⟩

/-- In any table with distinct rowids, two member rows with equal rowids are equal.
Proof sketch: their indices in the rowid list coincide because that list has no duplicates. -/
theorem Table.RowidsDistinct.row_eq {table : Table} (distinct : table.RowidsDistinct)
    {left right : Row} (first : left ∈ table.rows) (second : right ∈ table.rows)
    (same : left.rowid = right.rowid) : left = right := by
  obtain ⟨i, belowI, atI⟩ := List.mem_iff_getElem.mp first
  obtain ⟨j, belowJ, atJ⟩ := List.mem_iff_getElem.mp second
  have index : i = j := distinct.eq_of_getElem_eq (by simpa using belowI) (by simpa using belowJ) (by
    simp only [List.getElem_map]
    simpa only [atI, atJ] using same)
  subst j
  exact atI.symm.trans atJ

/-- For every located link and stored child row, an unsatisfied reference after deleting
a present parent row was already unsatisfied or matches that old row in the child scan.
The parent has stored rows and distinct rowids; row storage is aligned; lookup and scan
comparisons agree for all stored row pairs. Proof sketch: a lost lookup must have used the
removed row, and comparison consistency turns that witness into a scan match. -/
theorem ForeignKeyLink.unsatisfied_remove_parent {database : Database} {position : Nat} {parent : Table}
    (present : database.table position = some parent) (aligned : position < database.rows.length)
    (distinct : parent.RowidsDistinct) (stored : parent.RowsStored)
    (old : Row) (member : old ∈ parent.rows) (link : ForeignKeyLink) (key : ParentKey)
    (located : link.parent = .located position key) (child : CatalogTable) (row : Row)
    (childStored : row.Stored child.columns) (consistent : link.LookupScanConsistent child parent.shape key)
    (failed : link.satisfied (database.setRows position (parent.rows.filter (·.rowid != old.rowid))) row = false) :
    link.satisfied database row = false ∨ childMatches child parent.shape link key old row = true := by
  by_cases before : link.satisfied database row = true
  · have null : link.hasNull row.values = false := by
      cases null : link.hasNull row.values with
      | false => rfl
      | true => simp [ForeignKeyLink.satisfied, null] at failed
    have atShape : database.catalog.tableAt position = some parent.shape := by
      obtain ⟨shape, atShape, same⟩ := Option.map_eq_some_iff.mp present
      subst parent
      exact atShape
    have oldRows : database.rowsAt position = parent.rows := by simp [Database.rowsAt, present]
    have newRows : (database.setRows position (parent.rows.filter (·.rowid != old.rowid))).rowsAt position =
        parent.rows.filter (·.rowid != old.rowid) := by
      simp only [Database.rowsAt, Database.table_setRows _ present aligned, Option.map_some, Option.getD_some]
    have foundBefore : parentFound parent.shape key link row.values parent.rows none = true := by
      simpa only [ForeignKeyLink.satisfied, located, null, Bool.false_or, atShape, oldRows] using before
    have foundAfter : parentFound parent.shape key link row.values
        (parent.rows.filter (·.rowid != old.rowid)) none = false := by
      simpa only [ForeignKeyLink.satisfied, located, null, Bool.false_or, newRows,
        show (database.setRows position (parent.rows.filter (·.rowid != old.rowid))).catalog = database.catalog from rfl,
        atShape] using failed
    have lost := parentFound_remove_split parent.shape key link row.values parent.rows old
      (fun candidate inside equal => distinct.row_eq inside member equal) foundBefore
    rcases lost with kept | removed
    · rw [foundAfter] at kept
      contradiction
    · apply Or.inr
      rw [consistent old row (stored old member) childStored null]
      exact removed
  · exact .inl (Bool.eq_false_iff.mpr before)

end Belay.Sqlite.Model
