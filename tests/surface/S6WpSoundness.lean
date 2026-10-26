import S6Wp

set_option doc.verso true

/-! Connect the test-only transformer to S4 success and actual SQL execution. -/

namespace S6
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model (runScriptStep runScriptStep_others RunStep)

/-- For every program and context, the total-success transformer with an unrestricted
postcondition is exactly S4's success predicate, including actual raw and concrete alternative
continuations. Proof sketch: induction on the program; each definition uses the same step. -/
theorem check_top {α : Type} (program : Sql α) : ∀ state : Context,
    check true program (fun _ _ => True) state ↔
      program.SucceedsFrom state.clock state.index state.connection := by
  induction program with
  | pure value => intros; rfl
  | exec statement values rest later =>
    intro state
    simp only [check, Sql.SucceedsFrom]
    cases step : runScriptStep runContext state.clock state.index state.connection statement values with
    | ended reason => simp
    | continued output connection others =>
      refine forall_congr' fun found => forall_congr' fun _ => ?_
      obtain ⟨output, next⟩ := found
      unfold Sql.ExecutionSucceeds
      cases output <;> simp [later, Context.next]

/-- The context after the actual interpreter's run, retaining its clock and adding the
number and trace of statements that ran. This projection does not execute any statement. -/
def Context.finish {α : Type} (state : Context) (result : SqlRun α) : Context :=
  { state with
    index := state.index + result.outputs.length
    connection := result.connection
    outputs := state.outputs ++ result.outputs }

/-- For either error policy, every proved postcondition holds for the actual run's returned
value and full final context. In particular, a proved check cannot end without a value.
Proof sketch: induction on the program. Reuse its actual step and actual-output obligation;
the next context adds one index and output, which matches the interpreter's prefix. -/
theorem check_actual {α : Type} (reject : Bool) (program : Sql α) :
    ∀ (post : α → Context → Prop) (state : Context), check reject program post state →
      ∃ value, (program.runFrom state.clock state.index state.connection).value = some value ∧
        post value (state.finish (program.runFrom state.clock state.index state.connection)) := by
  induction program with
  | pure value =>
    intro post state holds
    exact ⟨value, rfl, by simpa [check, Context.finish, Sql.runFrom] using holds⟩
  | exec statement values rest later =>
    intro post state holds
    simp only [check] at holds
    cases step : runScriptStep runContext state.clock state.index state.connection statement values with
    | ended reason => simp [step] at holds
    | continued output connection others =>
      rw [step] at holds
      obtain rfl := runScriptStep_others step
      obtain ⟨value, returned, postHolds⟩ := later output post (state.next output connection)
        (holds { output, next := connection } (by simp [RunStep.executions])).2.1
      refine ⟨value, ?_, ?_⟩
      · simpa [Sql.runFrom, step, Context.next] using returned
      · simpa [Sql.runFrom, step, Context.finish, Context.next, List.append_assoc, Nat.add_assoc, Nat.add_comm]
          using postHolds

/-- A fresh proof context has the same environment and connection as the surface run. -/
def initial (db : Database) (env : Env) : Context :=
  ⟨env.clock, 0, db.raw.connection env.counters, []⟩

/-- For every database predicate and program, checking the unrestricted postcondition in
every complete environment is exactly {name}`Succeeds`. An unsatisfied database predicate
requires nothing. Proof sketch: apply {name}`check_top` at each initial context. -/
theorem check_complete_iff {α : Type} (program : Sql α) (predicate : Database → Prop) :
    (∀ db, predicate db → ∀ env : Env, env.Complete →
      check true program (fun _ _ => True) (initial db env)) ↔ Succeeds program predicate := by
  simp only [check_top, initial, Succeeds, Runnable.toSql, id_eq]

/-- For any program and initial context, a total-success check entails success of the actual
outputs. Proof sketch: weaken the postcondition to true using conjunctivity, then use S4's
{name}`Sql.SucceedsFrom.allOk`. -/
theorem check_allOk {α : Type} (program : Sql α) (post : α → Context → Prop)
    (state : Context) (holds : check true program post state) :
    (program.runFrom state.clock state.index state.connection).outputs.allOk = true := by
  have top : check true program (fun _ _ => True) state := by
    have pair := (check_and true program post (fun _ _ => True) state).mp
    exact (pair (by simpa using holds)).2
  exact Sql.SucceedsFrom.allOk _ _ _ _ ((check_top program state).mp top)

/-- A conditional-success claim permits modeled SQL errors and then requires no final
property, but still requires every continuation to remain modeled. An unmodeled branch
always fails. This is a candidate meaning, not production notation. -/
def ifOk {α : Type} (program : Sql α) (post : α → Context → Prop) (state : Context) : Prop :=
  check false program (fun value final => final.outputs.allOk = true → post value final) state

#print axioms check_top
#print axioms check_actual
#print axioms check_complete_iff
#print axioms check_allOk
end S6
