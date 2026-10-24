import Belay.Sqlite.Model.ForeignKeyLookupRemoval
import Belay.Sqlite.Model.ForeignKeyPhases
import Belay.Sqlite.Model.QueryLaws

set_option doc.verso true

/-! Row-count facts for physical deletion and the existing foreign-key scans. -/

namespace Belay.Sqlite.Model

/-- For every link and child row, replacing rows at a position that is not its located
parent leaves satisfaction unchanged. Missing and incompatible parents also remain unchanged.
Proof sketch: satisfaction reads only the selected parent's rows and the unchanged catalog. -/
theorem ForeignKeyLink.satisfied_setRows_other (link : ForeignKeyLink) (database : Database)
    (target : Nat) (rows : List Row) (row : Row)
    (untouched : ∀ parent key, link.parent = .located parent key → parent ≠ target) :
    link.satisfied (database.setRows target rows) row = link.satisfied database row := by
  cases selected : link.parent with
  | missing => simp [ForeignKeyLink.satisfied, selected]
  | mismatch parent => simp [ForeignKeyLink.satisfied, selected]
  | located parent key =>
    have same : (database.setRows target rows).rowsAt parent = database.rowsAt parent := by
      simp only [Database.rowsAt, database.table_setRows_other rows (untouched parent key selected)]
    simp only [ForeignKeyLink.satisfied, selected, same]
    rfl

/-- For every row predicate and member old row, removing all rows with its rowid reduces
the predicate count by at least one if the old row satisfies it, and by at least zero otherwise.
Duplicate rowids are allowed. Proof sketch: list induction isolates one removed occurrence. -/
theorem countP_remove_rowid (predicate : Row → Bool) (rows : List Row) (old : Row)
    (member : old ∈ rows) :
    (rows.filter (·.rowid != old.rowid)).countP predicate + (if predicate old then 1 else 0) ≤ rows.countP predicate := by
  induction rows with
  | nil => contradiction
  | cons first rest induction =>
    rcases List.mem_cons.mp member with same | later
    · subst first
      have smaller := (List.filter_sublist (p := fun row : Row => row.rowid != old.rowid) (l := rest)).countP_le (p := predicate)
      cases condition : predicate old <;> simp [condition] <;> omega
    · have smaller := induction later
      cases condition : predicate first <;> cases kept : first.rowid != old.rowid <;>
        simp [condition, kept] <;> omega

/-- For every present child and parent table, an existing parent scan with no extra rows
has the count of matching stored child rows, with the requested self-row exclusion.
Proof sketch: scan order is a permutation and does not change the filtered count. -/
theorem childRows_countP {database : Database} {link : ForeignKeyLink} {child : Table}
    (present : database.table link.child = some child) {position : Nat} {parent : CatalogTable}
    (parentAt : database.catalog.tableAt position = some parent) (key : ParentKey) (old : Row) (exclude : Bool) :
    (childRows database link key position old [] exclude).length =
      child.rows.countP (fun row => childMatches child.shape parent link key old row &&
        !(exclude && link.child == position && row.rowid == old.rowid)) := by
  simp only [childRows, present, parentAt, List.append_nil]
  rw [← List.countP_eq_length_filter]
  exact child.scanRows_perm.countP_eq _

end Belay.Sqlite.Model
