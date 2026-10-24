import Belay.Sqlite.Model.ForeignKeyRowPermutation
import Belay.Sqlite.Model.ForeignKeyCountInsert
import Belay.Sqlite.Model.AdmittedRowLaws

set_option doc.verso true

/-! The global replacement count follows from physical removal and append. -/

namespace Belay.Sqlite.Model

/-- For every aligned present table with distinct rowids and stored database rows,
replacing a member by a stored row gives the displayed violation-count bound. The replacement
must have distinct rowids and selected unique keys; scans and lookups must agree for every
stored row pair at the input table shapes, and each selected column mapping must name a unique
key. The bound adds old-child failures and new-parent repairs on the left, and old-parent
matches and new-child failures on the right. Proof sketch: compose physical removal and append
count laws, then transport through the in-place replacement permutation. -/
theorem Database.foreignKeyViolations_replace_parent {database : Database} {position : Nat} {table : Table}
    (present : database.table position = some table) (aligned : position < database.rows.length)
    (distinct : table.RowidsDistinct) (stored : database.RowsStored)
    (old new : Row) (member : old ∈ table.rows) (newStored : new.Stored table.shape.columns)
    (unique : (LiteralData.replaceRow table old new).KeysUnique (database.catalog.uniqueKeys position table.shape))
    (nextDistinct : (LiteralData.replaceRow table old new).RowidsDistinct)
    (consistent : ∀ link ∈ database.catalog.foreignKeyLinks, ∀ key child,
      link.parent = .located position key → database.table link.child = some child →
      link.LookupScanConsistent child.shape table.shape key)
    (selectedUnique : ∀ link ∈ database.catalog.foreignKeyLinks, ∀ pairs,
      link.parent = .located position (.columns pairs) →
      UniqueKey.ofColumns table.shape.columns (pairs.map Prod.snd) ∈ database.catalog.uniqueKeys position table.shape) :
    let removed := database.setRows position (table.rows.filter (·.rowid != old.rowid))
    let after := database.setRows position (LiteralData.replaceRow table old new).rows
    after.foreignKeyViolations +
      (childLinks database.catalog.foreignKeyLinks position).countP (fun link => !link.satisfied database old) +
      (database.catalog.foreignKeyLinks.map (parentInsertionMatches removed position new)).sum ≤
      database.foreignKeyViolations +
      (database.catalog.foreignKeyLinks.map (parentRemovalMatches database position old)).sum +
      (childLinks database.catalog.foreignKeyLinks position).countP (fun link => !link.satisfied after new) := by
  let remaining := table.rows.filter (·.rowid != old.rowid)
  let removed := database.setRows position remaining
  let next := database.setRows position (remaining ++ [new])
  have atRemoved : removed.table position = some { table with rows := remaining } :=
    Database.table_setRows remaining present aligned
  have alignedRemoved : position < removed.rows.length := by simpa [removed, Database.setRows] using aligned
  have tableRows : table.rows = database.rows.getD position [] := by
    obtain ⟨shape, _, equal⟩ := Option.map_eq_some_iff.mp present
    subst table
    rfl
  have storedRemoved : removed.RowsStored := by
    have preserved := rowsStoredLaws.sublist database position (fun rows => rows.filter (·.rowid != old.rowid))
      stored (fun _ => List.filter_sublist)
    simpa only [removed, remaining, tableRows] using preserved
  have comparisonRemoved : ∀ link ∈ database.catalog.foreignKeyLinks, ∀ key child,
      link.parent = .located position key → removed.table link.child = some child →
      link.LookupScanConsistent child.shape table.shape key := by
    intro link inside key child selected atChild
    by_cases self : link.child = position
    · rw [self, atRemoved, Option.some.injEq] at atChild
      subst child
      exact consistent link inside key table selected (self ▸ present)
    · rw [Database.table_setRows_other database remaining self] at atChild
      exact consistent link inside key child selected atChild
  have permuted : (LiteralData.replaceRow table old new).rows.Perm (remaining ++ [new]) :=
    replaceRow_perm_append table.rows old new distinct member
  have uniqueNext : ({ table with rows := remaining ++ [new] } : Table).KeysUnique
      (database.catalog.uniqueKeys position table.shape) := unique.perm permuted
  have distinctNext : ({ table with rows := remaining ++ [new] } : Table).RowidsDistinct :=
    (permuted.map Row.rowid).nodup_iff.mp nextDistinct
  have removedCount := Database.foreignKeyViolations_remove_parent present aligned distinct stored old member consistent
  have appendedCount := Database.foreignKeyViolations_append_parent atRemoved alignedRemoved storedRemoved new newStored
    uniqueNext distinctNext comparisonRemoved selectedUnique
  have afterAppend : removed.setRows position (remaining ++ [new]) = next := by
    simp only [removed, next, Database.setRows, List.set_set]
  rw [afterAppend] at appendedCount
  have rowPerm := database.rowsAt_setRows_perm present aligned permuted
  have countPerm := Database.foreignKeyViolations_rows_perm
    (before := database.setRows position (LiteralData.replaceRow table old new).rows) (after := next) rfl rowPerm
  have childPerm : (childLinks database.catalog.foreignKeyLinks position).countP
      (fun link => !link.satisfied (database.setRows position (LiteralData.replaceRow table old new).rows) new) =
      (childLinks database.catalog.foreignKeyLinks position).countP (fun link => !link.satisfied next new) := by
    apply List.countP_congr
    intro link _
    rw [ForeignKeyLink.satisfied_rows_perm
      (before := database.setRows position (LiteralData.replaceRow table old new).rows) (after := next) rfl rowPerm]
  dsimp only
  rw [childPerm, countPerm]
  change next.foreignKeyViolations +
    (childLinks database.catalog.foreignKeyLinks position).countP (fun link => !link.satisfied database old) +
    (database.catalog.foreignKeyLinks.map (parentInsertionMatches removed position new)).sum ≤ _
  change removed.foreignKeyViolations + _ ≤ _ at removedCount
  change next.foreignKeyViolations +
    (database.catalog.foreignKeyLinks.map (parentInsertionMatches removed position new)).sum =
    removed.foreignKeyViolations +
    (childLinks database.catalog.foreignKeyLinks position).countP (fun link => !link.satisfied next new) at appendedCount
  omega

end Belay.Sqlite.Model
