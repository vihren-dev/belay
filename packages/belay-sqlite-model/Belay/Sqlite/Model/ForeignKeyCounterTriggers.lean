import Belay.Sqlite.Model.ForeignKeyWorkConditions
set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For any good state and RAISE kind, the actual result obeys the foreign-key contract:
FAIL retains the bound, rollback retains database facts, IGNORE returns the state, and
raw errors impose nothing. Proof sketch: inspect the RAISE kind. -/
theorem raiseEffect_foreignKeyInvariant {profile : Profile} {catalog : Catalog} {state : KeyState}
    (good : KeyState.ForeignKeyInvariant profile catalog state) (kind : Syntax.RaiseKind) :
    ResultHolds (fun pair : KeyState × Bool => KeyState.ForeignKeyInvariant profile catalog pair.1) (KeyStop.ForeignKeyInvariant profile catalog) (raiseEffect state kind) := by
  cases kind <;> first | exact good | exact ⟨good.1, trivial⟩ | trivial

/-- For a nested runner that preserves the invariant, a matching frame and safe trigger
step preserve it on the actual success/stop result from any good input.
Proof sketch: inspect the step; UPDATE uses its assignment condition, queries retain rows,
and writes and RAISE use their existing result laws. -/
theorem runStep_counterBound {profile : Profile} {catalog : Catalog} {programs : List Resolved.Program} {nested : NestedRun}
    (keeps : nested.ForeignKeyKeeps profile catalog programs) (frame : RowFrame) (same : frame.programs = programs)
    (cells : List Value) {state : KeyState} (good : KeyState.ForeignKeyInvariant profile catalog state)
    (step : Resolved.Step) (safe : step.ForeignKeySafe catalog) :
    ResultHolds (fun pair : KeyState × Bool => KeyState.ForeignKeyInvariant profile catalog pair.1) (KeyStop.ForeignKeyInvariant profile catalog)
      (runStep catalog nested frame cells state step) := by
  cases step with
  | raise filter arms otherwise =>
    simp only [runStep]
    split
    · exact raiseEffect_foreignKeyInvariant good _
    · exact good
  | query query subqueries =>
    simp only [runStep]
    repeat' (first | split | dsimp only)
    all_goals first | trivial | exact good
  | insert | delete =>
    simp only [runStep]
    split
    · exact ResultHolds.bind (keeps _ _ _ same trivial good) fun _ reached => reached
    · trivial
  | update position assignments filter subqueries =>
    simp only [runStep]
    split
    · rename_i table atTable
      exact ResultHolds.bind (keeps _ _ _ same (safe table.shape (KeyState.table_shape atTable) _ cells) good)
        fun _ reached => reached
    · trivial

/-- For any good input and invariant-preserving nested runner, entering a trigger with
a matching frame has the stop contract; successful entry needs no state fact because it
returns unit. Proof sketch: entry executes an empty deletion and discards its result. -/
theorem enterProgram_counterBound {profile : Profile} {catalog : Catalog} {programs : List Resolved.Program} {nested : NestedRun}
    (keeps : nested.ForeignKeyKeeps profile catalog programs) (frame : RowFrame) (same : frame.programs = programs)
    (table : Nat) {state : KeyState} (good : KeyState.ForeignKeyInvariant profile catalog state) :
    ResultHolds (fun _ : Unit => True) (KeyStop.ForeignKeyInvariant profile catalog) (enterProgram nested frame table state) :=
  ResultHolds.map (keeps frame (.delete table [] false false false) state same trivial good) fun _ _ => trivial

/-- For any good input, a matching frame and trigger whose steps are safe, an
invariant-preserving nested runner gives an actual program result with the invariant.
Proof sketch: check entry and fold the body, retaining the fact after an ended sequence. -/
theorem runProgram_counterBound {profile : Profile} {catalog : Catalog} {programs : List Resolved.Program} {nested : NestedRun}
    (keeps : nested.ForeignKeyKeeps profile catalog programs) (frame : RowFrame) (same : frame.programs = programs)
    (cells : List Value) {state : KeyState} (good : KeyState.ForeignKeyInvariant profile catalog state)
    (program : Resolved.Program) (safe : ∀ step ∈ program.body, step.ForeignKeySafe catalog) :
    ResultHolds (fun pair : KeyState × Bool => KeyState.ForeignKeyInvariant profile catalog pair.1) (KeyStop.ForeignKeyInvariant profile catalog)
      (runProgram catalog nested frame cells state program) := by
  unfold runProgram
  split
  · exact good
  · refine ResultHolds.bind (enterProgram_counterBound keeps frame same program.table good) fun _ _ => ?_
    split
    · exact good
    · refine ResultHolds.foldlM_mem _ (fun pair step member good => ?_) (state, false) good
      obtain ⟨reached, ended⟩ := pair
      dsimp only
      split
      · exact good
      · exact runStep_counterBound keeps { frame with running := program.trigger :: frame.running } same cells good step (safe step member)

/-- For any good input and matching frame, safe supplied programs and a preserving
nested runner establish the invariant for the actual fired-program sequence.
Proof sketch: each fired program belongs to the supplied list; fold their result laws. -/
theorem runPrograms_counterBound {profile : Profile} {catalog : Catalog} {programs : List Resolved.Program} {nested : NestedRun}
    (keeps : nested.ForeignKeyKeeps profile catalog programs) (frame : RowFrame) (same : frame.programs = programs)
    (safe : ProgramsForeignKeySafe catalog programs) (table : Nat) (time : Syntax.TriggerTime)
    (event : Resolved.TriggerEvent) (cells : List Value) {state : KeyState} (good : KeyState.ForeignKeyInvariant profile catalog state) :
    ResultHolds (fun pair : KeyState × Bool => KeyState.ForeignKeyInvariant profile catalog pair.1) (KeyStop.ForeignKeyInvariant profile catalog)
      (runPrograms catalog nested frame table time event cells state) := by
  unfold runPrograms
  refine ResultHolds.foldlM_mem _ (fun pair program member good => ?_) (state, false) good
  obtain ⟨reached, ended⟩ := pair
  dsimp only
  split
  · exact good
  · apply runProgram_counterBound keeps frame same cells good program
    apply safe program
    rw [← same]
    exact (List.mem_filter.mp member).1

end Belay.Sqlite.Model
