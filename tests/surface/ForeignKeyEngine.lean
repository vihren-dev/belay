import Belay
import Belay.Sqlite.Model.ForeignKeyCounterWrites

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! The full row-engine theorem checks a real cascading UPDATE and an AFTER-trigger FAIL. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyEngineFixture

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

/-- The ordinary resolved UPDATE assignment, with the engine's real changed-column list. -/
def change (old : Row) : Row := LiteralData.movedRowid parent.rowidAlias
  (LiteralData.assign (.plain 0) parent.columns [(0, .literal (.integer 2))] old)

/-- Assignment coverage proves the raw work condition; callers do not assert final validity. -/
theorem updateSafe : RowWork.ForeignKeySafe input.raw.catalog
    (.update 0 change [0] (parent.changedColumns [0]) [1] true) := by
  apply ForeignKeyUpdateConditions.assignFrom parent rfl (.plain 0) _ (·.values)
  · intro cell _ column found
    have all : ∀ value ∈ parent.columns, value.generated = none := by decide +kernel
    exact all column (List.mem_of_getElem? found)
  · intro selected member
    change selected ∈ [link] at member
    simp only [List.mem_singleton] at member
    subst selected
    decide +kernel

/-- An optional AFTER UPDATE child trigger stops with FAIL after the cascade is stored. -/
def programs (failing : Bool) : List Resolved.Program :=
  if failing then [{ trigger := 2, table := 1, time := .after, event := .update none, width := 1, condition := none, body := [.raise none [] (some .fail)] }] else []

/-- Both rule sets enforce keys and leave enough depth for the actual cascade and trigger. -/
def rules (failing : Bool) : Resolved.WriteRules :=
  { keys := true, depth := 4, programs := programs failing }

/-- The same raw parent UPDATE runs with or without the AFTER trigger. -/
def run (failing : Bool) : KeyRun := rowsKeys (rules failing) 0 0
  (.update 0 change [0] (parent.changedColumns [0]) [1] true) input.raw true none

/-- The closed engine theorem proves row references for both success and retained FAIL rows. -/
theorem rowReferencesPreserved (failing : Bool) : (run failing).effect.Satisfies
    (fun result => result.RowReferencesHold result.catalog.foreignKeyMapping) := by
  apply rowsKeys_rowReferences (ready := ⟨input.valid.admitted, input.valid.unique⟩)
    (references := by decide +kernel) (enforced := rfl) (facts := comparisons)
  · cases failing <;> simp [ProgramsForeignKeySafe, Resolved.Step.ForeignKeySafe, rules, programs]
  · exact actions
  · intro fuel
    apply NestedRun.beforeUpdateFrame_of_empty
    intro position assigned
    cases failing <;> simp [RowFrame.fired, rules, programs]
  · exact updateSafe

/-- Successful execution updates both the parent and child, with two actual changes. -/
theorem successfulCascade : (match (run false).effect with
    | .ok database => (database.rowsAt 0).map (·.values) = [[.integer 2]] ∧
        (database.rowsAt 1).map (·.values) = [[.integer 2]] ∧ (run false).counts.total = 2
    | .error _ => False) := by exact ⟨rfl, rfl, rfl⟩

/-- FAIL publishes the already changed parent and child; it does not restore the input rows. -/
theorem retainedFail : (match (run true).effect with
    | .error (.constraintFail, database) => (database.rowsAt 0).map (·.values) = [[.integer 2]] ∧
        (database.rowsAt 1).map (·.values) = [[.integer 2]]
    | _ => False) := by exact ⟨rfl, rfl⟩

end ForeignKeyEngineFixture

#print axioms ForeignKeyEngineFixture.comparisons
#print axioms ForeignKeyEngineFixture.actions
#print axioms ForeignKeyEngineFixture.updateSafe
#print axioms ForeignKeyEngineFixture.rowReferencesPreserved
#print axioms ForeignKeyEngineFixture.successfulCascade
#print axioms ForeignKeyEngineFixture.retainedFail
