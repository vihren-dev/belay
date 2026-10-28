import Belay.Sqlite.MigrationPatternSuccess
import Belay.Sqlite.ExecutionViewMonad

set_option doc.verso true

namespace Belay.Sqlite.Migration

/-- A successful migration followed by a fixed pure application value has the same
weak observations as that pure value when only the migration segment is quiet.
Its connection and raw step count may differ. Proof sketch: every migration branch
returns with an empty quiet trace, and its pure continuation returns the fixed value. -/
theorem quiet_return_observation {μ α : Type} (migration : Sql μ) (value : α) (state : ExecutionContext)
    (success : migration.SucceedsFrom state.clock state.index state.connection) :
    ((Sql.View.quiet migration).bind (fun _ => .pure value) (fun _ => .pure value)).ObservationEquivAt
      (.pure value) state := by
  let view := (Sql.View.quiet migration).bind (fun _ => .pure value) (fun _ => .pure value)
  have constant result (branch : (migration.bind (fun _ => .pure value)).Branch
      state.clock state.index state.connection result) : view.observation result = (some value, []) := by
    obtain ⟨first, before, continuation⟩ := (Sql.branch_bind_iff migration (fun _ => .pure value) _ _ _ result).mp branch
    obtain ⟨returned, ok⟩ := (Sql.succeedsFrom_iff_branches _ _ _ _).mp success first before
    cases returnedValue : first.value with
    | none => simp [returnedValue] at returned
    | some resultValue =>
      simp only [returnedValue] at continuation
      obtain ⟨last, later, rfl⟩ := continuation
      have lastEq := (Sql.branch_pure_iff value _ _ _ last).mp later
      subst last
      apply Prod.ext
      · rfl
      · change ((Sql.View.quiet migration).bind (fun _ => .pure value) (fun _ => .pure value)).project
          (first.outputs ++ []) = []
        rw [Sql.View.project_bind_return before _ returnedValue]
        simp only [Sql.View.project, List.append_nil, Sql.View.project_quiet_of_allOk before ok]
  apply observationProfile_eq_iff.mpr
  constructor
  · exact constant _ (Sql.Branch.actual _ _ _ _)
  · intro seen
    constructor
    · rintro ⟨result, branch, equal⟩
      exact ⟨_, .pure value _ _ _, (constant result branch).symm.trans equal⟩
    · rintro ⟨result, branch, equal⟩
      have resultEq := (Sql.branch_pure_iff value _ _ _ result).mp branch
      subst result
      exact ⟨_, Sql.Branch.actual _ _ _ _, (constant _ (Sql.Branch.actual _ _ _ _)).trans equal⟩

/-- Running the application before a quiet migration preserves its weak observation
if the migration succeeds after every returning application branch at its exact raw
reached context. A stopped application still stops without running the migration.
This explicit sufficient premise does not change the pattern's original domain.
Proof sketch: replace each successful quiet tail by its remembered pure application
value, then use the program and view right-identity laws. -/
theorem before_observation {μ α : Type} (migration : Sql μ) (application : Sql α) (state : ExecutionContext)
    (success : ∀ result, application.Branch state.clock state.index state.connection result →
      ∀ value, result.value = some value →
        migration.SucceedsFrom state.clock (state.index + result.outputs.length) result.connection) :
    (beforeView application migration).ObservationEquivAt (Sql.View.identity application) state := by
  have compared := Sql.View.ObservationEquivOn.bind_same (Sql.View.identity application)
    (pre := fun context => context = state)
    (post := fun _ context => migration.SucceedsFrom context.clock context.index context.connection)
    (next := fun value => migration.bind fun _ => .pure value) (other := Sql.pure)
    (later := fun value => (Sql.View.quiet migration).bind (fun _ => .pure value) (fun _ => .pure value))
    (last := fun value => .pure value)
    (fun value context holds => quiet_return_observation migration value context holds)
    (by intro context equal result branch value returned; subst context; exact success result branch value returned)
  have identity := Sql.View.equiv_of_program_eq
    ((Sql.View.identity application).bind Sql.pure (fun value => .pure value))
    (Sql.View.identity application) ((Sql.bind_pure_map application id).trans (Sql.map_id application)) state
    (fun result _ => Sql.View.project_bind_pure _ result.outputs)
  exact (compared state rfl).trans identity.observation

end Belay.Sqlite.Migration
