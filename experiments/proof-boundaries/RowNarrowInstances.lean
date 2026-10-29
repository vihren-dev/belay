import RowNarrow
import Belay.Sqlite.Model.RowEngineTriggers
import Belay.Sqlite.Model.ForeignKeyCounterTriggers

set_option doc.verso true

open Belay.Sqlite.Model

namespace ProofBoundaries

/-- The database-invariant program claim retains its original assumptions. The shared program
traversal receives the existing entry and single-step facts; neither old program traversal is used. -/
theorem databaseProgramNarrow {invariant : Database → Prop} {catalog : Catalog} {nested : NestedRun}
    (keeps : nested.Keeps invariant catalog) (frame : RowFrame) (cells : List Value)
    {state : KeyState} (good : state.Holds invariant catalog) (program : Resolved.Program) :
    ProgramResult.Holds invariant catalog (runProgram catalog nested frame cells state program) :=
  programFromEffects catalog nested frame cells program good (enterProgram_holds keeps frame program.table good)
    (fun step _ _ held => runStep_holds keeps _ cells held step)

/-- The foreign-key program claim retains matching programs, safe steps and the full input
invariant. The shared traversal receives the existing local entry/step facts, whose stop
predicate distinguishes FAIL from rollback. It does not use either old program traversal. -/
theorem foreignKeyProgramNarrow {profile : Profile} {catalog : Catalog} {programs : List Resolved.Program}
    {nested : NestedRun} (keeps : nested.ForeignKeyKeeps profile catalog programs)
    (frame : RowFrame) (same : frame.programs = programs) (cells : List Value)
    {state : KeyState} (good : KeyState.ForeignKeyInvariant profile catalog state)
    (program : Resolved.Program) (safe : ∀ step ∈ program.body, step.ForeignKeySafe catalog) :
    ResultHolds (fun pair : KeyState × Bool => KeyState.ForeignKeyInvariant profile catalog pair.1)
      (KeyStop.ForeignKeyInvariant profile catalog) (runProgram catalog nested frame cells state program) :=
  programFromEffects catalog nested frame cells program good (enterProgram_counterBound keeps frame same program.table good)
    (fun step member _ held => runStep_counterBound keeps
      { frame with running := program.trigger :: frame.running } same cells held step (safe step member))

/-- The database-invariant fired-program claim has the original assumptions. The proof supplies
the shared single-program result to the shared fired-list traversal. -/
theorem databaseProgramsNarrow {invariant : Database → Prop} {catalog : Catalog} {nested : NestedRun}
    (keeps : nested.Keeps invariant catalog) (frame : RowFrame) (table : Nat)
    (time : Syntax.TriggerTime) (event : Resolved.TriggerEvent) (cells : List Value)
    {state : KeyState} (good : state.Holds invariant catalog) :
    ProgramResult.Holds invariant catalog (runPrograms catalog nested frame table time event cells state) :=
  programsFromEffects catalog nested frame table time event cells
    (fun program _ _ held => databaseProgramNarrow keeps frame cells held program) good

/-- The foreign-key fired-program claim has the original matching-frame and program-safety
assumptions. Fired-list membership supplies each body's safety facts, while the two shared
traversals preserve the separate success and stop predicates. -/
theorem foreignKeyProgramsNarrow {profile : Profile} {catalog : Catalog} {programs : List Resolved.Program}
    {nested : NestedRun} (keeps : nested.ForeignKeyKeeps profile catalog programs)
    (frame : RowFrame) (same : frame.programs = programs) (safe : ProgramsForeignKeySafe catalog programs)
    (table : Nat) (time : Syntax.TriggerTime) (event : Resolved.TriggerEvent) (cells : List Value)
    {state : KeyState} (good : KeyState.ForeignKeyInvariant profile catalog state) :
    ResultHolds (fun pair : KeyState × Bool => KeyState.ForeignKeyInvariant profile catalog pair.1)
      (KeyStop.ForeignKeyInvariant profile catalog)
      (runPrograms catalog nested frame table time event cells state) := by
  apply programsFromEffects catalog nested frame table time event cells _ good
  intro program member _ held
  apply foreignKeyProgramNarrow keeps frame same cells held program
  apply safe program
  rw [← same]
  exact (List.mem_filter.mp member).1

#print axioms databaseProgramNarrow
#print axioms foreignKeyProgramNarrow
#print axioms databaseProgramsNarrow
#print axioms foreignKeyProgramsNarrow

end ProofBoundaries
