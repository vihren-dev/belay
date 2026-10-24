import Belay
import Belay.Sqlite.Model.ForeignKeyDropCatalog

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! Enforced DROP applies implicit DELETE effects before transporting the surviving foreign-key declarations. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyEnforcedDropFixture

/-- A non-self BLOB-affinity link with a real child that SET NULL must retain. -/
def input : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY);
  CREATE TABLE c(x REFERENCES p(k) ON DELETE SET NULL);
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- The parent shape removed by DROP. -/
def parent : CatalogTable := (input.raw.catalog.tableAt 0).getD { columns := [] }

/-- The child shape whose selected first column receives the action. -/
def child : CatalogTable := (input.raw.catalog.tableAt 1).getD { columns := [] }

/-- The single actual selected link. -/
def link : ForeignKeyLink := input.raw.catalog.foreignKeyLinks.headD
  { child := 1
    key := { table := .ofString "p", columns := [0], referenced := [.ofString "k"], onDelete := .setNull, onUpdate := .noAction }
    parent := .located 0 (.columns [(0,0)]) }

/-- The schema comparisons hold for all stored row values, not just the initial integer. -/
theorem comparisons : input.raw.catalog.ForeignKeyComparisons := by
  constructor
  · intro selected member position key childShape parentShape located childAt parentAt
    change selected ∈ [link] at member
    simp only [List.mem_singleton] at member
    subst selected
    change ParentLink.located 0 (.columns [(0,0)]) = .located position key at located
    cases located
    have cs : childShape = child := Option.some.inj (childAt.symm.trans rfl)
    have ps : parentShape = parent := Option.some.inj (parentAt.symm.trans rfl)
    subst childShape; subst parentShape
    exact ForeignKeyLink.lookupScanConsistent_blob link child parent 0 0
      (child.columns.headD { name := .ofString "x", declaredType := none })
      (parent.columns.headD { name := .ofString "k", declaredType := none }) rfl rfl rfl rfl
  · intro selected member position pairs parentShape located parentAt
    change selected ∈ [link] at member
    simp only [List.mem_singleton] at member
    subst selected
    change ParentLink.located 0 (.columns [(0,0)]) = .located position (.columns pairs) at located
    cases located
    have same : parentShape = parent := Option.some.inj (parentAt.symm.trans rfl)
    subst parentShape
    decide +kernel
  · intro selected member key shape located _
    change selected ∈ [link] at member
    simp only [List.mem_singleton] at member
    subst selected
    cases located

/-- All generated action updates cover their selected cells and have no stale self scan. -/
theorem actions : ActionsForeignKeySafe input.raw.catalog := by
  intro selected member action _ active position parentPosition key parentShape childShape new cells located _ childAt made
  change selected ∈ [link] at member
  simp only [List.mem_singleton] at member
  subst selected
  change ParentLink.located 0 (.columns [(0,0)]) = .located parentPosition key at located
  cases located
  have same : childShape = child := Option.some.inj (childAt.symm.trans rfl)
  subst childShape
  constructor
  · intro shape found
    have same : shape = child := Option.some.inj (found.symm.trans rfl)
    subst shape
    apply RowChange.Covers.of_setCells
    · intro pair inside
      apply child.assigned_mem_changedColumns
      rw [← actionCells_positions active made]
      exact List.mem_map.mpr ⟨pair, inside, rfl⟩
    · intro cell _ column found
      have all : ∀ value ∈ child.columns, value.generated = none := by decide +kernel
      exact all column (List.mem_of_getElem? found)
  · intro _ _ _ _ selected member
    change selected ∈ ([] : List ForeignKeyLink).filter _ at member
    simp at member

/-- Enforced rules without triggers retain every BEFORE target frame. -/
def rules : Resolved.WriteRules := { keys := true, depth := 4 }

/-- The schema's universal comparisons and mapped-action facts establish the actual rules. -/
theorem ruleConditions : rules.ForeignKeyConditions Profile.pinned input.raw.catalog := by
  refine ⟨rfl, comparisons, ?_, actions, ?_⟩
  · intro program member
    cases member
  · intro fuel
    apply NestedRun.beforeUpdateFrame_of_empty
    intro position assigned
    rfl

/-- The actual implicit DELETE result, before the parent catalog entry is removed. -/
def deleted : Model.Database := effectDatabase
  (rowsKeys rules 0 0 (.delete 0 [1] false true false) input.raw true).effect

/-- After implicit deletion the parent is empty and the child remains with a NULL key. -/
theorem deleteRows : deleted.rowsAt 0 = [] ∧ (deleted.rowsAt 1).map (·.values) = [[.null]] := by exact ⟨rfl, rfl⟩

/-- The only surviving declaration belongs to the child; the implicit DELETE retained its schema. -/
theorem declaration (position : Nat) (table : Table) (present : deleted.table position = some table)
    (declared : candidate ∈ table.shape.allForeignKeys) : position = 1 ∧ candidate = link.key := by
  have bound := Database.table_lt present
  change position < 2 at bound
  have choices : position = 0 ∨ position = 1 := by omega
  rcases choices with rfl | rfl
  all_goals change some _ = some table at present
  all_goals cases present
  · change candidate ∈ [] at declared; cases declared
  · change candidate ∈ [link.key] at declared
    exact ⟨rfl, List.mem_singleton.mp declared⟩

/-- Emptiness forces selected NULL before catalog removal; the missing-parent fallback retains it. -/
theorem removedParentFrame : deleted.DropForeignKeyFrame [0] deleted.catalog.foreignKeyMapping
    (deleted.catalog.drop [0]).foreignKeyMapping := by
  intro position table present kept candidate declared
  obtain ⟨rfl, rfl⟩ := declaration position table present declared
  left
  intro row member
  apply ForeignKeyLink.hasNull_unresolved_of_empty_parent (database := deleted) (link := link)
    (parent := 0) (comparison := .columns [(0,0)]) rfl rfl deleteRows.1
  · have holds : deleted.RowReferencesHold deleted.catalog.foreignKeyMapping := by decide +kernel
    exact holds 1 table present link.key declared row member
  · rfl
  · intro position key located
    change ParentLink.missing = .located position key at located
    cases located

/-- The public row theorem retains real child rows after SET NULL and then removes the parent. -/
theorem dropRows : (runStatement 0 {} [] (.drop [0] (some rules)) input.raw).effect.Satisfies
    (fun result => result.RowReferencesHold result.catalog.foreignKeyMapping) := by
  apply runStatement_drop_enforced_rowReferences rules 0 {} [] [0]
    ⟨input.valid.admitted, input.valid.unique⟩ (by decide +kernel) ruleConditions
  · intro target table head found after ran
    have targetIs : target = 0 := Option.some.inj head.symm
    subst target
    have tableIs : table = { shape := parent, rows := input.raw.rowsAt 0 } := Option.some.inj found.symm
    subst table
    have same : after = deleted := Except.ok.inj ran.symm
    subst after
    exact removedParentFrame
  · intro absent
    cases absent

/-- Successful parent removal preserves the row atom but fails the independent schema atom. -/
theorem dropSeparatesAtoms : (match (runStatement 0 {} [] (.drop [0] (some rules)) input.raw).effect with
    | .ok after => after.RowReferencesHold after.catalog.foreignKeyMapping ∧
      ¬after.ParentSchemasCompatible after.catalog.foreignKeyMapping ∧
      (after.rowsAt 0).map (·.values) = [[.null]]
    | .error _ => False) := by
  change (deleted.drop [0]).RowReferencesHold (deleted.drop [0]).catalog.foreignKeyMapping ∧
    ¬(deleted.drop [0]).ParentSchemasCompatible (deleted.drop [0]).catalog.foreignKeyMapping ∧
    ((deleted.drop [0]).rowsAt 0).map (·.values) = [[.null]]
  decide +kernel

/-- Dropping the populated child retains both atoms through the combined public engine rule. -/
theorem childDropAtoms : (runStatement 0 {} [] (.drop [1] (some rules)) input.raw).effect.Satisfies
    (fun result => result.ParentSchemasCompatible result.catalog.foreignKeyMapping ∧
      result.RowReferencesHold result.catalog.foreignKeyMapping) := by
  apply runStatement_drop_enforced_foreignKeyAtoms rules 0 {} [] [1]
    ⟨input.valid.admitted, input.valid.unique⟩ (by decide +kernel) ruleConditions
  all_goals
    intro position shape found kept candidate declared
    have present : deleted.table position = some { shape, rows := deleted.rows.getD position [] } := by
      change (input.raw.catalog.tableAt position).map _ = _
      rw [found]; rfl
    obtain ⟨rfl, _⟩ := declaration position _ present declared
    contradiction

end ForeignKeyEnforcedDropFixture
#print axioms ForeignKeyEnforcedDropFixture.comparisons
#print axioms ForeignKeyEnforcedDropFixture.actions
#print axioms ForeignKeyEnforcedDropFixture.ruleConditions
#print axioms ForeignKeyEnforcedDropFixture.deleteRows
#print axioms ForeignKeyEnforcedDropFixture.declaration
#print axioms ForeignKeyEnforcedDropFixture.removedParentFrame
#print axioms ForeignKeyEnforcedDropFixture.childDropAtoms
#print axioms ForeignKeyEnforcedDropFixture.dropRows
#print axioms ForeignKeyEnforcedDropFixture.dropSeparatesAtoms
#print axioms Belay.Sqlite.Model.Database.RowReferencesHold.drop_of_null_or_kept
#print axioms Belay.Sqlite.Model.ForeignKeyLink.hasNull_declared
#print axioms Belay.Sqlite.Model.ForeignKeyLink.hasNull_of_empty_parent
#print axioms Belay.Sqlite.Model.ForeignKeyLink.hasNull_unresolved_of_empty_parent
#print axioms Belay.Sqlite.Model.dropKeys_rowReferences
#print axioms Belay.Sqlite.Model.runStatement_drop_enforced_rowReferences
#print axioms Belay.Sqlite.Model.dropKeys_parentSchemasCompatible
#print axioms Belay.Sqlite.Model.runStatement_drop_enforced_parentSchemasCompatible
#print axioms Belay.Sqlite.Model.runStatement_drop_enforced_foreignKeyAtoms
