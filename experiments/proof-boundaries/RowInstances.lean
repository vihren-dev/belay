import RowControl
import Belay.Sqlite.Model.ForeignKeyWorkConditions

set_option doc.verso true

open Belay.Sqlite.Model

namespace ProofBoundaries

/-- Database predicates satisfy trigger-control facts: bookkeeping keeps rows, stopped states
retain the database predicate, and ordinary errors impose no condition. The proof reduces the
database projection and checks the stop constructors. -/
theorem databaseControlFacts (invariant : Database → Prop) (catalog : Catalog) :
    RowControlFacts (KeyState.Holds invariant catalog) (KeyStop.Holds invariant catalog) where
  afterStep _ _ _ good := good
  queried _ _ good := good
  undescribed := trivial
  error _ _ _ := trivial
  stopped _ _ good := good

/-- If every work item is permitted, every trigger step satisfies the generated-work premise.
The proof inspects the step and returns the unconditional permission. -/
theorem allStepsAllowed {P : KeyState → Prop} (catalog : Catalog) (frame : RowFrame)
    (cells : List Value) (step : Resolved.Step) : StepAllowed P (fun _ _ _ => True) catalog frame cells step := by
  cases step <;> simp only [StepAllowed] <;> intros <;> trivial

/-- The existing database preservation claim for fired programs follows from the shared
control proof with no extra entry assumptions. The proof supplies unconditional work permission
and the database bookkeeping facts; it does not call the old trigger traversal theorems. -/
theorem databasePrograms {invariant : Database → Prop} {catalog : Catalog} {nested : NestedRun}
    (keeps : nested.Keeps invariant catalog) (frame : RowFrame) (table : Nat)
    (time : Syntax.TriggerTime) (event : Resolved.TriggerEvent) (cells : List Value)
    {state : KeyState} (good : state.Holds invariant catalog) :
    ProgramResult.Holds invariant catalog (runPrograms catalog nested frame table time event cells state) := by
  apply rowPrograms catalog nested frame table time event cells (P := KeyState.Holds invariant catalog)
    (Q := KeyStop.Holds invariant catalog) _ good
  intro program _ reached held
  apply rowProgram (databaseControlFacts invariant catalog)
    (allowed := fun _ _ _ => True) (fun frame work state _ good => keeps frame work state good)
    catalog frame cells held program trivial
  exact fun step _ => allStepsAllowed catalog _ cells step

/-- Foreign-key control needs a matching program list and safe raw work. These conditions
read the frame and work; the explicit state argument leaves state-dependent permissions available. -/
def foreignKeyAllowed (catalog : Catalog) (programs : List Resolved.Program)
    (frame : RowFrame) (work : RowWork) (_state : KeyState) : Prop :=
  frame.programs = programs ∧ work.ForeignKeySafe catalog

/-- Foreign-key success and stop predicates satisfy trigger-control facts. FAIL retains the
full invariant; rollback needs only admission and unique keys. The proof reduces bookkeeping
fields and checks the two explicit stop algorithms separately. -/
theorem foreignKeyControlFacts (profile : Profile) (catalog : Catalog) :
    RowControlFacts (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog) where
  afterStep _ _ _ good := good
  queried _ _ good := good
  undescribed := ⟨trivial, trivial⟩
  error _ _ _ := ⟨trivial, trivial⟩
  stopped algorithm _ good := by
    cases algorithm with
    | fail => exact good
    | rollback => exact ⟨good.1, trivial⟩

/-- A safe trigger step in a matching frame generates permitted foreign-key work for every
good state. The proof checks each constructor; UPDATE obtains the actual shape from its
successful lookup and applies the existing assignment-safety premise. -/
theorem foreignKeyStepAllowed {profile : Profile} {catalog : Catalog} {programs : List Resolved.Program}
    (frame : RowFrame) (same : frame.programs = programs) (cells : List Value)
    (step : Resolved.Step) (safe : step.ForeignKeySafe catalog) :
    StepAllowed (KeyState.ForeignKeyInvariant profile catalog) (foreignKeyAllowed catalog programs)
      catalog frame cells step := by
  cases step with
  | raise | query => trivial
  | insert | delete => exact fun _ _ _ _ => ⟨same, trivial⟩
  | update position assignments filter subqueries =>
    intro state table _ found
    exact ⟨same, safe table.shape (KeyState.table_shape found) _ cells⟩

/-- The existing foreign-key claim for fired programs follows from the shared control proof
with the original matching-frame, program-safety and input-invariant assumptions. The proof
uses each fired program's list membership to establish its step permissions. -/
theorem foreignKeyPrograms {profile : Profile} {catalog : Catalog} {programs : List Resolved.Program}
    {nested : NestedRun} (keeps : nested.ForeignKeyKeeps profile catalog programs)
    (frame : RowFrame) (same : frame.programs = programs) (safe : ProgramsForeignKeySafe catalog programs)
    (table : Nat) (time : Syntax.TriggerTime) (event : Resolved.TriggerEvent) (cells : List Value)
    {state : KeyState} (good : KeyState.ForeignKeyInvariant profile catalog state) :
    ResultHolds (fun pair : KeyState × Bool => KeyState.ForeignKeyInvariant profile catalog pair.1)
      (KeyStop.ForeignKeyInvariant profile catalog)
      (runPrograms catalog nested frame table time event cells state) := by
  apply rowPrograms catalog nested frame table time event cells _ good
  intro program member reached held
  apply rowProgram (foreignKeyControlFacts profile catalog)
    (allowed := foreignKeyAllowed catalog programs)
    (fun frame work state permitted good => keeps frame work state permitted.1 permitted.2 good)
    catalog frame cells held program ⟨same, trivial⟩
  intro step inside
  apply foreignKeyStepAllowed _ same cells step
  apply safe program _ step inside
  rw [← same]
  exact (List.mem_filter.mp member).1

#print axioms databasePrograms
#print axioms foreignKeyPrograms

end ProofBoundaries
