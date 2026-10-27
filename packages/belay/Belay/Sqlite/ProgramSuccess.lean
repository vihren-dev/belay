import Belay.Sqlite.Success
import Belay.Sqlite.ProgramLaws

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite Belay.Sqlite.Model

/-- For every output list, {name}`List.allOk` is true exactly when every member is neither
an error nor an output that ends a run. Proof sketch: expand the Boolean list check. -/
theorem List.allOk_iff (outputs : List Output) :
    outputs.allOk = true ↔ ∀ output ∈ outputs, output.isError = false ∧ output.endsRun = false := by
  simp [List.allOk]

/-- For every program, clock, index and connection, success on every branch implies that
the actual run's outputs have no error and none ends the run. Proof sketch: induction on
the program. A successful step continues without error, and its actual-output continuation
is one of the branches required to succeed. -/
theorem Sql.SucceedsFrom.allOk {α : Type} (program : Sql α) :
    ∀ (clock : Option Clock) (index : Nat) (connection : Connection),
      program.SucceedsFrom clock index connection →
        (program.runFrom clock index connection).outputs.allOk = true := by
  induction program with
  | pure value => intro clock index connection _; rfl
  | exec statement values rest later =>
    intro clock index connection success
    simp only [Sql.runFrom]
    cases step : runScriptStep runContext clock index connection statement values with
    | ended reason => simp [Sql.SucceedsFrom, step] at success
    | continued output next others =>
      simp only [Sql.SucceedsFrom, step] at success
      replace success := success { output, next } (by simp [RunStep.executions])
      unfold Sql.ExecutionSucceeds at success
      have continues := (runScriptStep_continued step).2
      have tail := later output clock (index + 1) next success.2.1
      simpa [List.allOk, success.1, continues] using tail

/-- For every successful script or program, every database satisfying its predicate, and
every complete environment, all outputs of the actual public run are successful.
Proof sketch: {name}`Sql.SucceedsFrom.allOk` covers the actual continuation, and
{name}`Sql.run_outputs` identifies the public output field. -/
theorem Succeeds.allOk {σ α : Type} [Runnable σ α] {program : σ} {predicate : Database → Prop}
    (success : Succeeds program predicate) {db : Database} (holds : predicate db)
    {env : Env} (complete : env.Complete) : (db.run program env).outputs.allOk = true := by
  change ((Runnable.toSql program).run db env).outputs.allOk = true
  rw [Sql.run_outputs]
  exact Sql.SucceedsFrom.allOk _ _ _ _ (success db holds env complete)

/-- For every function, program, clock, index and connection, mapping the final value leaves
success unchanged. Proof sketch: induction on the program; each statement has the same
output and every actual or alternative continuation has the induction equivalence. -/
theorem Sql.succeedsFrom_map {α β : Type} (function : α → β) (program : Sql α) :
    ∀ (clock : Option Clock) (index : Nat) (connection : Connection),
      (program.map function).SucceedsFrom clock index connection ↔
        program.SucceedsFrom clock index connection := by
  induction program with
  | pure value => intro clock index connection; rfl
  | exec statement values rest later =>
    intro clock index connection
    simp only [Sql.map, Sql.SucceedsFrom]
    split
    · rfl
    · rename_i output next others step
      simp only [later]

end Belay.Sqlite
