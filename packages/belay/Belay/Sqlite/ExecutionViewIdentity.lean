import Belay.Sqlite.ExecutionViewEquivalenceLaws

set_option doc.verso true

namespace Belay.Sqlite

/-- Identity views compare weakly exactly when the ordinary executions compare by
return value and trace. Proof sketch: identity projection leaves every trace unchanged. -/
theorem Sql.View.identity_observation_iff {α : Type} (first second : Sql α)
    (state : ExecutionContext) :
    (identity first).ObservationEquivAt (identity second) state ↔ first.ObservationEquivAt second state := by
  constructor <;> intro same <;> constructor
  · simpa [observation, project_identity, SqlRun.observation] using same.actual
  · simpa [observation, project_identity, SqlRun.observation] using same.branches
  · simpa [observation, project_identity, SqlRun.observation] using same.actual
  · simpa [observation, project_identity, SqlRun.observation] using same.branches

/-- At a shared context, identity full observations determine the exact complete run,
including its raw trace and connection. Proof sketch: the returned value, connection and
trace fields are equal, and the shared starting trace cancels. -/
theorem Sql.View.identity_full_eq_iff {α : Type} (first second : Sql α)
    (state : ExecutionContext) (one two : SqlRun α) :
    (identity first).fullObservation state one = (identity second).fullObservation state two ↔ one = two := by
  constructor
  · intro same
    have value := congrArg Prod.fst same
    have connection := congrArg (fun result => result.2.connection) same
    have outputs := congrArg (fun result => result.2.outputs) same
    simp only [fullObservation, finish_identity, ExecutionContext.finish, List.append_cancel_left_eq] at outputs
    cases one with
    | mk one valueOne =>
      cases one
      cases two with
      | mk two valueTwo =>
        cases two
        simp only [fullObservation, finish_identity, ExecutionContext.finish] at value connection
        cases value
        cases connection
        cases outputs
        rfl
  · rintro rfl
    simp [fullObservation, finish_identity]

/-- Identity full comparison is exactly ordinary complete execution equivalence.
Actual runs and all branch results agree in either formulation. Proof sketch:
identity full observations determine their raw results, so branch matching is exact. -/
theorem Sql.View.identity_equiv_iff {α : Type} (first second : Sql α) (state : ExecutionContext) :
    (identity first).EquivAt (identity second) state ↔ first.EquivAt second state := by
  constructor
  · intro same
    refine ⟨(identity_full_eq_iff first second state _ _).mp same.actual, ?_⟩
    intro result
    constructor
    · intro branch
      obtain ⟨other, matched, equal⟩ := (same.branches _).mp ⟨result, branch, rfl⟩
      cases (identity_full_eq_iff second first state _ _).mp equal
      exact matched
    · intro branch
      obtain ⟨other, matched, equal⟩ := (same.branches _).mpr ⟨result, branch, rfl⟩
      cases (identity_full_eq_iff first second state _ _).mp equal
      exact matched
  · intro same
    constructor
    · exact (identity_full_eq_iff first second state _ _).mpr same.actual
    · intro observation
      constructor
      · rintro ⟨result, branch, seen⟩
        exact ⟨result, (same.branches result).mp branch, by simpa [fullObservation, finish_identity] using seen⟩
      · rintro ⟨result, branch, seen⟩
        exact ⟨result, (same.branches result).mpr branch, by simpa [fullObservation, finish_identity] using seen⟩

end Belay.Sqlite
