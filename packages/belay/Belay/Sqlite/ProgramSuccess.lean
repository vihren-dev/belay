import Belay.Sqlite.Success

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite Belay.Sqlite.Model

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
    simp only [Sql.SucceedsFrom, Sql.runFrom] at success ⊢
    cases step : runScriptStep runContext clock index connection statement values with
    | ended reason => simp [step] at success
    | continued output next =>
      rw [step] at success
      have continues := (runScriptStep_continued step).2
      have tail := later output clock (index + 1) next success.2.1
      simpa [List.allOk, success.1, continues] using tail

/-- For every program, database and environment, the public run's outputs equal the
underlying run's outputs. The validity check cannot append an invalid-result output.
Proof sketch: {name}`Sql.runFrom_database_valid` selects the valid branch of
{name}`Run.checked`. -/
theorem Sql.run_outputs {α : Type} (program : Sql α) (db : Database) (env : Env) :
    (program.run db env).outputs =
      (program.runFrom env.clock 0 (db.raw.connection env.counters)).outputs := by
  simp only [Sql.run, Run.checked, dite_eq_left (Sql.runFrom_database_valid program db env)]

/-- For every successful script or program, every database satisfying its predicate, and
every complete environment, all outputs of the actual public run are successful.
Proof sketch: {name}`Sql.SucceedsFrom.allOk` covers the actual continuation, and
{name}`Sql.run_outputs` removes the redundant validity check. -/
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
    · rename_i output next step
      simp only [later]

end Belay.Sqlite
