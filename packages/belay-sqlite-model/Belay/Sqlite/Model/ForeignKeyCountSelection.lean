import Belay.Sqlite.Model.ForeignKeyCountReplace
import Belay.Sqlite.Model.ForeignKeyReplaceFrame

set_option doc.verso true

/-! Unchanged contributions cancel when UPDATE processes only selected foreign keys. -/

namespace Belay.Sqlite.Model

/-- For every Boolean pair equal outside a selected sublist, their full and selected
counts satisfy the displayed cancellation equality. -/
private theorem countP_cancel_filter {α : Type} (items : List α) (selected old new : α → Bool)
    (same : ∀ item ∈ items, selected item = false → old item = new item) :
    items.countP old + (items.filter selected).countP new =
      items.countP new + (items.filter selected).countP old := by
  induction items with
  | nil => rfl
  | cons first rest induction =>
    have remaining := induction (fun item member => same item (by simp [member]))
    cases chosen : selected first with
    | false =>
      have equal := same first (by simp) chosen
      simp [List.countP_cons, chosen, equal]
      omega
    | true => simp [List.countP_cons, chosen]; omega

/-- For every natural-valued pair equal outside a selected sublist, their full and
selected sums satisfy the displayed cancellation equality. -/
private theorem sum_cancel_filter {α : Type} (items : List α) (selected : α → Bool) (old new : α → Nat)
    (same : ∀ item ∈ items, selected item = false → old item = new item) :
    (items.map old).sum + ((items.filter selected).map new).sum =
      (items.map new).sum + ((items.filter selected).map old).sum := by
  induction items with
  | nil => rfl
  | cons first rest induction =>
    have remaining := induction (fun item member => same item (by simp [member]))
    cases chosen : selected first with
    | false =>
      have equal := same first (by simp) chosen
      simp [chosen, equal]
      omega
    | true => simp [chosen]; omega

/-- For every aligned parent and present child table, two parent rows agreeing on their
key have equal old/new scan lengths when the old row is physically removed. The old scan
excludes its self row; the new scan reads no stale row. Proof sketch: other-table rows stay,
while a self scan's exclusion equals the removal filter. -/
theorem childRows_unchanged_parent {database : Database} {position : Nat} {parent child : Table}
    (present : database.table position = some parent) (aligned : position < database.rows.length)
    (link : ForeignKeyLink) (key : ParentKey) (childAt : database.table link.child = some child)
    (old new : Row) (sameKey : key.RowAgrees old new) :
    (childRows database link key position old [] true).length =
      (childRows (database.setRows position (parent.rows.filter (·.rowid != old.rowid)))
        link key position new [] false).length := by
  have parentAt : database.catalog.tableAt position = some parent.shape := by
    obtain ⟨shape, parentAt, equal⟩ := Option.map_eq_some_iff.mp present
    subst parent
    exact parentAt
  let removed := database.setRows position (parent.rows.filter (·.rowid != old.rowid))
  by_cases self : link.child = position
  · have childSame : child = parent := by rw [self, present] at childAt; exact Option.some.inj childAt.symm
    subst child
    have nextChild : removed.table link.child = some { parent with rows := parent.rows.filter (·.rowid != old.rowid) } := by
      rw [self]
      exact Database.table_setRows _ present aligned
    rw [childRows_countP childAt parentAt, childRows_countP nextChild parentAt]
    simp only [self, beq_self_eq_true, Bool.true_and, Bool.false_and, Bool.not_false, Bool.and_true,
      List.countP_filter, childMatches_congr_parent_key sameKey]
    rfl
  · have nextChild : removed.table link.child = some child := by
      rw [Database.table_setRows_other database _ self]
      exact childAt
    rw [childRows_countP childAt parentAt, childRows_countP nextChild parentAt]
    have different : (link.child == position) = false := beq_eq_false_iff_ne.mpr self
    simp only [different, childMatches_congr_parent_key sameKey, Bool.true_and, Bool.false_and,
      Bool.not_false, Bool.and_true]

/-- For every catalog link and aligned present target table, removing an old row and
using a new row with the same selected parent key gives equal old/new scan contributions.
Links to other positions, or without a located parent, need no key equality and contribute zero.
Proof sketch: the selected child table exists, and its unchanged-key scan lengths agree. -/
theorem parentMatches_unchanged {database : Database} {position : Nat} {parent : Table}
    (present : database.table position = some parent) (aligned : position < database.rows.length)
    (old new : Row) (link : ForeignKeyLink) (member : link ∈ database.catalog.foreignKeyLinks)
    (agrees : ∀ key, link.parent = .located position key → key.RowAgrees old new) :
    parentRemovalMatches database position old link =
      parentInsertionMatches (database.setRows position (parent.rows.filter (·.rowid != old.rowid))) position new link := by
  cases selected : link.parent with
  | missing | mismatch other => simp [parentRemovalMatches, parentInsertionMatches, selected]
  | located other key =>
    by_cases equal : other = position
    · subst other
      have childMember : link ∈ childLinks database.catalog.foreignKeyLinks link.child := by
        simp only [childLinks, List.mem_reverse, List.mem_filter, beq_self_eq_true, and_true]
        exact member
      obtain ⟨_, _, shape, atShape, _⟩ := (database.catalog.mem_childLinks_iff _ _).mp childMember
      let child : Table := {shape, rows := database.rows.getD link.child []}
      have atChild : database.table link.child = some child := by simp only [Database.table, atShape, Option.map_some, child]
      simp only [parentRemovalMatches, parentInsertionMatches, selected, ite_true]
      exact childRows_unchanged_parent present aligned link key atChild old new (agrees key selected)
    · simp [parentRemovalMatches, parentInsertionMatches, selected, equal]

/-- Under the full replacement-count law's storage, rowid, uniqueness and comparison
premises, the same bound holds with selected child and parent checks only. Every omitted child
must keep its projection and any self-parent key; every omitted parent must keep its selected
key. Proof sketch: unchanged checks have equal old/new contributions, which cancel from the
full equation. The selections may be empty and may preserve duplicate links. -/
theorem Database.foreignKeyViolations_replace_selected {database : Database} {position : Nat} {table : Table}
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
      UniqueKey.ofColumns table.shape.columns (pairs.map Prod.snd) ∈ database.catalog.uniqueKeys position table.shape)
    (chooseChild chooseParent : ForeignKeyLink → Bool)
    (unchangedChild : ∀ link ∈ childLinks database.catalog.foreignKeyLinks position,
      chooseChild link = false → link.ChildAgrees old new ∧
        ∀ key, link.parent = .located position key → key.RowAgrees old new)
    (unchangedParent : ∀ link ∈ database.catalog.foreignKeyLinks, chooseParent link = false →
      ∀ key, link.parent = .located position key → key.RowAgrees old new) :
    let removed := database.setRows position (table.rows.filter (·.rowid != old.rowid))
    let after := database.setRows position (LiteralData.replaceRow table old new).rows
    after.foreignKeyViolations +
      ((childLinks database.catalog.foreignKeyLinks position).filter chooseChild).countP (fun link => !link.satisfied database old) +
      ((database.catalog.foreignKeyLinks.filter chooseParent).map (parentInsertionMatches removed position new)).sum ≤
      database.foreignKeyViolations +
      ((database.catalog.foreignKeyLinks.filter chooseParent).map (parentRemovalMatches database position old)).sum +
      ((childLinks database.catalog.foreignKeyLinks position).filter chooseChild).countP (fun link => !link.satisfied after new) := by
  have all := Database.foreignKeyViolations_replace_parent present aligned distinct stored old new member newStored
    unique nextDistinct consistent selectedUnique
  have children := countP_cancel_filter (childLinks database.catalog.foreignKeyLinks position) chooseChild
    (fun link => !link.satisfied database old)
    (fun link => !link.satisfied (database.setRows position (LiteralData.replaceRow table old new).rows) new) (by
      intro link inside inactive
      have unchanged := unchangedChild link inside inactive
      rw [unchanged.1.satisfied database,
        ForeignKeyLink.satisfied_replace_parent_frame present aligned distinct old new member link new unchanged.2])
  have parents := sum_cancel_filter database.catalog.foreignKeyLinks chooseParent
    (parentRemovalMatches database position old)
    (parentInsertionMatches (database.setRows position (table.rows.filter (·.rowid != old.rowid))) position new) (by
      intro link inside inactive
      exact parentMatches_unchanged present aligned old new link inside (unchangedParent link inside inactive))
  dsimp only at all ⊢
  omega

/-- For every link list, target and predicate, selecting parent links after filtering
equals filtering the selected parent links. Proof sketch: the filters commute through reversal. -/
theorem parentLinks_filter (links : List ForeignKeyLink) (position : Nat) (choose : ForeignKeyLink → Bool) :
    parentLinks (links.filter choose) position = (parentLinks links position).filter choose := by
  simp [parentLinks, List.filter_filter, Bool.and_comm]

end Belay.Sqlite.Model
