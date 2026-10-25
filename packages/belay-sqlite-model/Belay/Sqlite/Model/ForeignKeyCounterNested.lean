import Belay.Sqlite.Model.ForeignKeyWorkConditions
set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For any state transformation that keeps rows and the immediate counter, mapping it
over a result preserves the foreign-key success/stop contract. Proof sketch: combine the
database-fact and counter mapping laws, including FAIL and rollback carriers. -/
theorem KeyResult.mapState_foreignKeyInvariant {profile : Profile} {catalog : Catalog} {change : KeyState → KeyState}
    (rows : ∀ state, (change state).rows = state.rows) (counter : ∀ state, (change state).counter = state.counter)
    {result : Except KeyStop KeyState} (good : ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog) result) :
    ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog) (KeyResult.mapState change result) :=
  (KeyResult.mapState_holds rows (good.imp (fun _ pair => pair.1) (fun _ pair => pair.1))).and
    (KeyResult.mapState_counterBound rows counter (good.imp (fun _ pair => pair.2) (fun _ pair => pair.2)))

/-- If a nested runner preserves the foreign-key invariant for matching safe work, its
credited wrapper does too. Proof sketch: resetting/restoring statement counts keeps rows
and the immediate foreign-key counter on both success and stop branches. -/
theorem NestedRun.credited_foreignKeyKeeps {profile : Profile} {catalog : Catalog}
    {programs : List Resolved.Program} {nested : NestedRun}
    (keeps : nested.ForeignKeyKeeps profile catalog programs) :
    (NestedRun.credited nested).ForeignKeyKeeps profile catalog programs := by
  intro frame work state same safe good
  have ran := keeps frame work { state with own := 0 } same safe good
  unfold NestedRun.credited
  dsimp only
  cases result : nested frame work { state with own := 0 } with
  | error stop =>
    rw [result] at ran
    exact KeyResult.mapState_foreignKeyInvariant (change := fun reached : KeyState =>
      { reached with own := state.own, inserted := state.inserted }) (fun _ => rfl) (fun _ => rfl) ran
  | ok reached =>
    rw [result] at ran
    exact ran

/-- For a selected action on a catalog link, a matching frame, good input, safe generated
actions and a preserving nested runner, actual action execution has the invariant.
Proof sketch: inspect the actual action; writes use their generated-work condition and
nested contract, while skipped or undescribed branches preserve the result contract. -/
theorem runAction_foreignKeyInvariant {profile : Profile} {catalog : Catalog} {programs : List Resolved.Program} {nested : NestedRun}
    (keeps : nested.ForeignKeyKeeps profile catalog programs) (frame : RowFrame) (same : frame.programs = programs)
    (safe : ActionsForeignKeySafe catalog) (link : ForeignKeyLink) (inside : link ∈ catalog.foreignKeyLinks)
    (action : Syntax.ForeignKeyAction) (selected : action = link.key.onDelete ∨ action = link.key.onUpdate)
    (position : Nat) (old : Row) (new : Option Row) {state : KeyState} (good : KeyState.ForeignKeyInvariant profile catalog state) :
    ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog)
      (runAction catalog (nested frame.action) link action position old new state) := by
  unfold runAction
  repeat' (first | split | dsimp only)
  all_goals first | exact good | trivial | skip
  all_goals
    refine ResultHolds.map (keeps frame.action _ state same ?_ good) ?_
    · first
      | trivial
      | exact safe link inside _ selected (by simp) position _ _ _ _ _ _
          (by assumption) (by assumption) (by assumption) (by assumption)
    · intro reached good
      exact good

end Belay.Sqlite.Model
