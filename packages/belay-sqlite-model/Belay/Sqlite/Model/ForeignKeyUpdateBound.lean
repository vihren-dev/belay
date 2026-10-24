import Belay.Sqlite.Model.ForeignKeyCountSelection
import Belay.Sqlite.Model.ForeignKeyStaleLookup
import Belay.Sqlite.Model.ForeignKeyInsertBound

set_option doc.verso true

/-! The global FK counter bound through the actual successful UPDATE check phases. -/

namespace Belay.Sqlite.Model

/-- For every state with the global FK counter bound, successful actual old/new checks
around physical removal bound the violations of the final in-place replacement by the returned
counter. Rows are aligned and stored; the old row is present with distinct rowids; the stored
replacement has distinct rowids and selected unique keys. Scans agree with lookups for all
stored pairs at the table shapes. Omitted child and parent checks preserve their read cells;
self shortcuts and retained stale lookups are sound. Either there is no stale row or every
processed parent link reads a different child table. This last condition excludes SQLite's
stale self scan that can cancel an unrelated pending violation. Stops and later actions or
triggers are outside this successful-phase law. Proof sketch: the selected replacement count
bound and actual old/new counter deltas compose directly; no bound is required while the old
row is temporarily absent. -/
theorem updateChecks_replace_bound {catalog : Catalog} {state before checked : KeyState}
    {position : Nat} {table : Table}
    (bound : state.CounterBound catalog) (present : (state.database catalog).table position = some table)
    (aligned : position < state.rows.length) (distinct : table.RowidsDistinct)
    (stored : (state.database catalog).RowsStored)
    (old new : Row) (member : old ∈ table.rows) (newStored : new.Stored table.shape.columns)
    (unique : (LiteralData.replaceRow table old new).KeysUnique (catalog.uniqueKeys position table.shape))
    (nextDistinct : (LiteralData.replaceRow table old new).RowidsDistinct)
    (consistent : ∀ link ∈ catalog.foreignKeyLinks, ∀ key child,
      link.parent = .located position key → (state.database catalog).table link.child = some child →
      link.LookupScanConsistent child.shape table.shape key)
    (selectedUnique : ∀ link ∈ catalog.foreignKeyLinks, ∀ pairs,
      link.parent = .located position (.columns pairs) →
      UniqueKey.ofColumns table.shape.columns (pairs.map Prod.snd) ∈ catalog.uniqueKeys position table.shape)
    (chooseChild chooseParent : ForeignKeyLink → Bool)
    (unchangedChild : ∀ link ∈ childLinks catalog.foreignKeyLinks position,
      chooseChild link = false → link.ChildAgrees old new ∧
        ∀ key, link.parent = .located position key → key.RowAgrees old new)
    (unchangedParent : ∀ link ∈ catalog.foreignKeyLinks, chooseParent link = false →
      ∀ key, link.parent = .located position key → key.RowAgrees old new)
    (stale : Option Row) (changed : List Nat)
    (selfSound : ∀ link ∈ (childLinks catalog.foreignKeyLinks position).filter chooseChild,
      ∀ key, link.parent = .located position key → link.SelfLookupSound table.shape key)
    (staleSound : ∀ link ∈ (childLinks catalog.foreignKeyLinks position).filter chooseChild,
      ∀ key, link.parent = .located position key →
        ∀ previous ∈ staleRows key stale changed, key.RowAgrees previous new)
    (noStaleScan : stale = none ∨ ∀ link ∈ (parentLinks catalog.foreignKeyLinks position).filter chooseParent,
      link.child ≠ position)
    (oldResult : oldSteps catalog state position old
      ((childLinks catalog.foreignKeyLinks position).filter chooseChild)
      ((parentLinks catalog.foreignKeyLinks position).filter chooseParent) false = .ok before)
    (newResult : newSteps catalog (before.changeRows position (fun rows => rows.filter (·.rowid != old.rowid))) position new
      ((childLinks catalog.foreignKeyLinks position).filter chooseChild)
      ((parentLinks catalog.foreignKeyLinks position).filter chooseParent) true stale changed = .ok checked) :
    (((state.database catalog).setRows position (LiteralData.replaceRow table old new).rows).foreignKeyViolations : Int) ≤
      checked.counter := by
  let children := (childLinks catalog.foreignKeyLinks position).filter chooseChild
  let parents := (parentLinks catalog.foreignKeyLinks position).filter chooseParent
  let removed := (state.database catalog).setRows position (table.rows.filter (·.rowid != old.rowid))
  have tableRows : table.rows = state.rows.getD position [] := by
    obtain ⟨shape, _, equal⟩ := Option.map_eq_some_iff.mp present
    subst table
    rfl
  have oldRows := oldSteps_rows catalog state position old children parents false
  rw [oldResult] at oldRows
  dsimp only [ResultHolds] at oldRows
  have removedSame : (before.changeRows position (fun rows => rows.filter (·.rowid != old.rowid))).database catalog = removed := by
    simp only [KeyState.database, KeyState.changeRows, Database.setRows, removed, oldRows, tableRows]
  have replaceCount := Database.foreignKeyViolations_replace_selected present aligned distinct stored
    old new member newStored unique nextDistinct consistent selectedUnique chooseChild chooseParent unchangedChild unchangedParent
  dsimp only at replaceCount
  rw [parentRemovalMatches_sum, parentInsertionMatches_sum, parentLinks_filter] at replaceCount
  have childrenCount : children.countP
      (fun link => !link.satisfied ((state.database catalog).setRows position (LiteralData.replaceRow table old new).rows) new) ≤
      children.countP (fun link => !newRowSatisfied removed position new stale changed link) := by
    apply List.countP_mono_left
    intro link inside failed
    have sound := ForeignKeyLink.newRowSatisfied_replace present aligned distinct old new member newStored link stale changed
      (selfSound link inside) (staleSound link inside)
    cases accepted : newRowSatisfied removed position new stale changed link with
    | false => rfl
    | true => simp [sound accepted] at failed
  have oldDelta := oldSteps_counter_delta catalog state position old children parents false
  rw [oldResult] at oldDelta
  dsimp only [ResultHolds] at oldDelta
  have newDelta := newSteps_counter_delta catalog
    (before.changeRows position (fun rows => rows.filter (·.rowid != old.rowid))) position new children parents true stale changed
  rw [newResult] at newDelta
  dsimp only [ResultHolds] at newDelta
  rw [removedSame] at newDelta
  have scans : parentDecrements removed position new stale parents = parentDecrements removed position new none parents := by
    rcases noStaleScan with empty | separate
    · rw [empty]
    · exact parentDecrements_without_stale_self removed position new stale parents separate
  rw [scans] at newDelta
  simp only [ite_true, KeyState.changeRows] at newDelta
  unfold KeyState.CounterBound at bound
  change (_ : Int) ≤ state.counter at bound
  change _ + children.countP _ + parentDecrements removed position new none parents ≤
    _ + parentIncrements (state.database catalog) position old parents + children.countP _ at replaceCount
  omega

end Belay.Sqlite.Model
