import Belay.Sqlite.ExecutionStep
import Belay.Sqlite.ProgramSuccess

set_option doc.verso true

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- Every branch remains modeled, has an error-free whole trace, and satisfies the final
property. The whole trace includes the supplied prefix; an error or unmodeled output in
that prefix makes this false.
Use an initial context with an empty trace for a fresh-run success claim. -/
abbrev Sql.andOk {α : Type} (program : Sql α) (post : α → ExecutionContext → Prop)
    (state : ExecutionContext) : Prop :=
  program.check (fun value final => final.outputs.allOk = true ∧ post value final) state

/-- Every branch remains modeled and satisfies the final property if its whole trace is
error-free. An error or unmodeled output in the existing prefix removes the final-property
obligation. Every branch of this program must still remain modeled: a new unmodeled stop
makes the check false. Use an empty prefix to condition only this fresh run. -/
abbrev Sql.ifOk {α : Type} (program : Sql α) (post : α → ExecutionContext → Prop)
    (state : ExecutionContext) : Prop :=
  program.check (fun value final => final.outputs.allOk = true → post value final) state

/-- Checking an error-free final trace is exactly an error-free prefix and S4 success from
the supplied clock, index and connection. This quantifies both raw and concrete branches.
Proof sketch: induction on the program; the finite step law appends each chosen output,
while S4 success checks its error flag and the same continuations. -/
theorem Sql.check_allOk_iff {α : Type} (program : Sql α) : ∀ state : ExecutionContext,
    program.check (fun _ final => final.outputs.allOk = true) state ↔
      state.outputs.allOk = true ∧ program.SucceedsFrom state.clock state.index state.connection := by
  induction program with
  | pure value => intro state; simp [Sql.check_pure, Sql.SucceedsFrom]
  | exec statement values rest later =>
    intro state
    rw [Sql.check_exec]
    simp only [Sql.SucceedsFrom]
    cases step : runScriptStep runContext state.clock state.index state.connection statement values with
    | ended reason => simp
    | continued output connection =>
      have continues := (runScriptStep_continued step).2
      have nextOk (seen : Output) : (state.next seen connection).outputs.allOk = true ↔
          state.outputs.allOk = true ∧ seen.isError = false ∧ seen.endsRun = false := by
        simp only [ExecutionContext.next, List.allOk, List.all_append, List.all_cons,
          List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true']
      simp only [later, nextOk]
      cases output <;> simp_all [ExecutionContext.next, Output.isError, Output.endsRun, and_assoc]


/-- Total success with a true final property is exactly the prefix condition and S4 success
from this full context. Proof sketch: remove the true conjunct and apply the trace theorem. -/
theorem Sql.andOk_true_iff {α : Type} (program : Sql α) (state : ExecutionContext) :
    program.andOk (fun _ _ => True) state ↔ state.outputs.allOk = true ∧
      program.SucceedsFrom state.clock state.index state.connection := by
  simpa [Sql.andOk] using program.check_allOk_iff state

/-- At an empty prefix, total success with a true final property is exactly S4 success at
the same clock, index and full connection. Proof sketch: the empty trace is error-free. -/
theorem Sql.andOk_empty_iff {α : Type} (program : Sql α) (state : ExecutionContext)
    (empty : state.outputs = []) : program.andOk (fun _ _ => True) state ↔
      program.SucceedsFrom state.clock state.index state.connection := by
  simpa [empty, List.allOk] using program.andOk_true_iff state

/-- Total success implies the conditional policy at the same context for every final
property. Proof sketch: each branch's conjunction implies the corresponding implication. -/
theorem Sql.andOk_ifOk {α : Type} {program : Sql α} {post : α → ExecutionContext → Prop}
    {state : ExecutionContext} (total : program.andOk post state) : program.ifOk post state :=
  Sql.check_mono total (fun _ _ both _ => both.2)

/-- Across all databases satisfying a predicate and every complete environment, fresh
true-postcondition total success is exactly S4's universal success claim. An unsatisfied
database predicate imposes no obligation. Proof sketch: apply the empty-prefix bridge at
each initial context; no default environment replaces the quantified environment. -/
theorem Sql.andOk_complete_iff {α : Type} (program : Sql α) (predicate : Database → Prop) :
    (∀ db, predicate db → ∀ env : Env, env.Complete →
      program.andOk (fun _ _ => True) (ExecutionContext.initial db env)) ↔ Succeeds program predicate := by
  constructor
  · intro checked db holds env complete
    exact (program.andOk_empty_iff (ExecutionContext.initial db env) rfl).mp (checked db holds env complete)
  · intro success db holds env complete
    exact (program.andOk_empty_iff (ExecutionContext.initial db env) rfl).mpr (success db holds env complete)

end Belay.Sqlite
