import Belay
import Belay.Sqlite.Model.ForeignKeyRuns

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! Statement laws derive the engine premises from actual assignments and check each enforced write family. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyStatementFixture

/-- A non-self BLOB-affinity link with a real child to cascade. -/
def input : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(k PRIMARY KEY);
  CREATE TABLE c(x REFERENCES p(k) ON UPDATE CASCADE);
  INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);"

/-- The parent shape whose first column changes. -/
def parent : CatalogTable := (input.raw.catalog.tableAt 0).getD { columns := [] }

/-- The child shape whose selected first column receives the action. -/
def child : CatalogTable := (input.raw.catalog.tableAt 1).getD { columns := [] }

/-- The single actual selected link. -/
def link : ForeignKeyLink := input.raw.catalog.foreignKeyLinks.headD
  { child := 1
    key := { table := .ofString "p", columns := [0], referenced := [.ofString "k"], onDelete := .noAction, onUpdate := .cascade }
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

/-- All generated CASCADE updates cover their selected cells and have no stale self scan. -/
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

/-- A resolved UPDATE of the parent key exercises the real cascade. -/
def update : Resolved.Statement := .update 0 [(0, .literal (.integer 2))] none [] [] (some rules)

/-- The public statement condition uses column definitions and scan positions, not final row truth. -/
theorem updateCondition : update.ForeignKeyRowsCondition Profile.pinned input.raw := by
  refine ⟨⟨input.valid.admitted, input.valid.unique⟩, ruleConditions, ?_, ?_⟩
  · intro shape found cell _ column atColumn
    have same : shape = parent := Option.some.inj (found.symm.trans rfl)
    subst shape
    have all : ∀ value ∈ parent.columns, value.generated = none := by decide +kernel
    exact all column (List.mem_of_getElem? atColumn)
  · intro name shape found _ selected member
    have selectedShape : input.raw.catalog.tableAt 0 = some shape := by
      simp only [Catalog.tableAt, found]
    have same : shape = parent := Option.some.inj (selectedShape.symm.trans rfl)
    subst shape
    have inside := (List.mem_filter.mp member).1
    change selected ∈ [link] at inside
    simp only [List.mem_singleton] at inside
    subst selected
    decide +kernel

/-- Both independent atoms survive the actual cascading statement under the supplied mapping. -/
theorem updatePreserves : (runStatement 0 {} [] update input.raw).effect.Satisfies
    (fun result => result.ParentSchemasCompatible input.raw.catalog.foreignKeyMapping ∧
      result.RowReferencesHold input.raw.catalog.foreignKeyMapping) :=
  runStatement_foreignKeyAtoms Profile.pinned _ 0 {} [] update (by decide +kernel) updateCondition

/-- The preserved UPDATE is successful and changes both stored key cells. -/
theorem updateRows : (match (runStatement 0 {} [] update input.raw).effect with
    | .ok database => (database.rowsAt 0).map (·.values) = [[.integer 2]] ∧
        (database.rowsAt 1).map (·.values) = [[.integer 2]]
    | .error _ => False) := by exact ⟨rfl, rfl⟩

/-- INSERT, DELETE and UPSERT DO NOTHING exercise the other enforced statement constructors. -/
def writes : List Resolved.Statement :=
  [.insert 1 [[.value (.integer 1)]] [] [] (some rules), .delete 1 none [] [] (some rules),
   .upsert 0 [[.value (.integer 1)]] [{ target := none, action := .nothing }] [] none [] (some rules)]

/-- Every listed write uses the public statement theorem, with no final-row premise. -/
theorem writesPreserve (statement : Resolved.Statement) (member : statement ∈ writes) :
    (runStatement 0 {} [] statement input.raw).effect.Satisfies
      (fun result => result.RowReferencesHold result.catalog.foreignKeyMapping) := by
  apply runStatement_rowReferences (profile := Profile.pinned) 0 {} [] statement (by decide +kernel)
  simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact ⟨⟨input.valid.admitted, input.valid.unique⟩, ruleConditions⟩

/-- All three listed constructors really succeed, with change counts one, one and zero. -/
theorem writeOutcomes : (writes.map fun statement =>
    let result := runStatement 0 {} [] statement input.raw
    (result.effect.isOk, result.counts.changes)) = [(true, some 1), (true, some 1), (true, some 0)] := by rfl

/-- Enforced UPSERT DO UPDATE is currently undescribed, unlike the successful DO NOTHING case. -/
theorem doUpdateUndescribed : (runStatement 0 {} []
    (.upsert 0 [[.value (.integer 1)]] [{ target := none, action := .update [(0, .literal (.integer 2))] none }]
      [] none [] (some rules)) input.raw).effect = .error (.unmodeled, input.raw) := by rfl

end ForeignKeyStatementFixture

#print axioms ForeignKeyStatementFixture.comparisons
#print axioms ForeignKeyStatementFixture.actions
#print axioms ForeignKeyStatementFixture.ruleConditions
#print axioms ForeignKeyStatementFixture.updateCondition
#print axioms ForeignKeyStatementFixture.updatePreserves
#print axioms ForeignKeyStatementFixture.updateRows
#print axioms ForeignKeyStatementFixture.writesPreserve
#print axioms ForeignKeyStatementFixture.writeOutcomes
#print axioms ForeignKeyStatementFixture.doUpdateUndescribed
