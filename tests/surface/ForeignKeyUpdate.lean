import Belay
import Belay.Sqlite.Model.ForeignKeyUpdateBound

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! UPDATE checks cover changed child keys, and a separate frame covers unchanged keys. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyUpdateFixture

/-- A parent and child with an independent payload column. -/
def input : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(f REFERENCES p,x);
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1,0);"

/-- The present child table before the update. -/
def target : Table := (input.raw.table 1).getD { shape := { columns := [] }, rows := [] }

/-- The schema's only FK link, to a different table. -/
def link : ForeignKeyLink := input.raw.catalog.foreignKeyLinks.headD
  { child := 1
    key := { table := .ofString "p", columns := [0], referenced := [], onDelete := .noAction, onUpdate := .noAction }
    parent := .located 0 (.columns [(0,0)]) }

/-- The existing child row. -/
def old : Row := { rowid := 1, values := [.integer 1, .integer 0] }

/-- Setting the child key to NULL exempts this row from its reference. -/
def new : Row := { old with values := [.null, .integer 0] }

/-- Before checks keep this initial state; new checks keep the temporary removed-row state. -/
def initial : KeyState := { rows := input.raw.rows }

/-- The actual temporary state used between UPDATE's two FK phases. -/
def removed : KeyState := initial.changeRows 1 (fun rows => rows.filter (·.rowid != old.rowid))

/-- The generic phase law establishes the bound for the real child-to-NULL checks.
The irrelevant target-parent premises are discharged from the catalog, not final row truth. -/
theorem changedChildBound :
    (((input.raw.setRows 1 (LiteralData.replaceRow target old new).rows).foreignKeyViolations : Nat) : Int) ≤
      removed.counter := by
  refine updateChecks_replace_bound (catalog := input.raw.catalog) (state := initial)
    (before := initial) (checked := removed) (position := 1) (table := target)
    (KeyState.CounterBound.start (database := input.raw) (by decide +kernel)) rfl (by decide +kernel)
    (by unfold Table.RowidsDistinct; decide +kernel) input.valid.admitted.rowsStored old new (by decide +kernel) (by decide +kernel)
    (by change (LiteralData.replaceRow target old new).KeysUnique []; intro key member; contradiction)
    (by unfold Table.RowidsDistinct; decide +kernel) ?_ ?_ (fun _ => true) (fun _ => true)
    (by intros; contradiction) (by intros; contradiction) (some old) [0] ?_ ?_ (.inr ?_) rfl rfl
  · intro found member key child selected _
    change found ∈ [link] at member
    simp only [List.mem_singleton] at member
    subst found
    cases selected
  · intro found member pairs selected
    change found ∈ [link] at member
    simp only [List.mem_singleton] at member
    subst found
    cases selected
  · intro found member key selected
    change found ∈ [link] at member
    simp only [List.mem_singleton] at member
    subst found
    cases selected
  · intro found member key selected
    change found ∈ [link] at member
    simp only [List.mem_singleton] at member
    subst found
    cases selected
  · intro found member
    change found ∈ ([] : List ForeignKeyLink) at member
    contradiction

/-- With a zero returned counter, the checked child-to-NULL replacement has valid references. -/
theorem changedChildReferences :
    (input.raw.setRows 1 (LiteralData.replaceRow target old new).rows).RowReferencesHold input.raw.catalog.foreignKeyMapping := by
  apply (Database.foreignKeyViolations_zero _).mp
  have bounded := changedChildBound
  change (_ : Int) ≤ 0 at bounded
  omega

/-- Changing only the payload preserves the exact violation count through the generic frame.
This includes self-parent keys in general; this fixture has an external parent. -/
theorem payloadCount :
    (input.raw.setRows 1 (LiteralData.replaceRow target old { old with values := [.integer 1, .integer 99] }).rows).foreignKeyViolations =
      input.raw.foreignKeyViolations := by
  apply Database.foreignKeyViolations_replace_unchanged (table := target) rfl (by decide +kernel)
    (by unfold Table.RowidsDistinct; decide +kernel) old _ (by decide +kernel)
  · intro found member
    change found ∈ [link] at member
    simp only [List.mem_singleton] at member
    subst found
    intro position member
    change position ∈ [0] at member
    simp only [List.mem_singleton] at member
    subst position
    rfl
  · intro found member key selected
    change found ∈ [link] at member
    simp only [List.mem_singleton] at member
    subst found
    cases selected

/-- The parsed, resolved UPDATEs execute both the zero-check payload and changed-child cases. -/
theorem resolvedUpdates :
    let result := input.raw.run (sql "PRAGMA foreign_keys=ON; UPDATE c SET x=99; UPDATE c SET f=NULL;")
    result.outputs = [.done 0, .done 1, .done 1] ∧ result.connection.state.database.foreignKeyViolations = 0 := by
  decide +kernel

end ForeignKeyUpdateFixture

#print axioms ForeignKeyUpdateFixture.changedChildBound
#print axioms ForeignKeyUpdateFixture.changedChildReferences
#print axioms ForeignKeyUpdateFixture.payloadCount
#print axioms ForeignKeyUpdateFixture.resolvedUpdates
#print axioms parentFound_congr_parent_key
#print axioms parentFound_congr_child_values
#print axioms parentCell_congr_parent_key
#print axioms childMatches_congr_parent_key
#print axioms ForeignKeyLink.ChildAgrees.hasNull
#print axioms ForeignKeyLink.ChildAgrees.satisfied
#print axioms parentFound_stale_rows
#print axioms ForeignKeyLink.newRowSatisfied_append_stale
#print axioms staleRows_agree
#print axioms parentDecrements_without_stale_self
#print axioms parentFound_perm
#print axioms ForeignKeyLink.satisfied_rows_perm
#print axioms Database.foreignKeyViolations_rows_perm
#print axioms Table.KeysUnique.perm
#print axioms replaceRow_perm_append
#print axioms Database.rowsAt_setRows_perm
#print axioms parentFound_replace_key
#print axioms ForeignKeyLink.satisfied_replace_parent_frame
#print axioms Database.foreignKeyViolations_replace_unchanged
#print axioms Database.foreignKeyViolations_replace_parent
#print axioms childRows_unchanged_parent
#print axioms parentMatches_unchanged
#print axioms Database.foreignKeyViolations_replace_selected
#print axioms parentLinks_filter
#print axioms ForeignKeyLink.newRowSatisfied_replace
#print axioms updateChecks_replace_bound
