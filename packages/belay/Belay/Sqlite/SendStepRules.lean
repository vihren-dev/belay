import Belay.Sqlite.PlainInsertEffect

set_option doc.verso true

/-!
The step of one sent statement at any context (ADR 0017, S6). The rules of
{lit}`Belay.Sqlite.PlainInsertEffect` and its siblings start a fresh run. The rules built on this module work at
the context that a program has reached, so a program of several statements needs one rule for each
statement, not one proof for the whole program.
-/

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- The connection after a statement that changes the stored database and the counters and nothing else:
the connection with the database, and with the counters after the counts of the statement. The snapshot of
an open transaction, the clock assignment and the settings stay. A successful plain write and a failed
write both give this connection. -/
def Model.Connection.afterWrite (connection : Connection) (database : Model.Database) (counts : Counts) : Connection :=
  { connection with state := { connection.state with
      database, counters := connection.state.counters.apply counts } }

/-- For every context, statement, values and post: a program that sends the one statement checks the post
when the step of the statement continues and the post holds after the step. The statement can be any
statement whose output is never a choice. In plain words, this rule turns the check of a send into a claim
about the connection that the step reaches. Proof sketch: {name}`check_send_single_of_step` for the
step, with the choice excluded by the premise. -/
theorem Sql.check_send_of_step {ctx : ExecutionContext} {statement : Syntax.Statement} {values : List Value}
    {post : List Output → ExecutionContext → Prop}
    (modeled : ∃ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others)
    (notChoice : ∀ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others →
        ∀ alternatives, output ≠ .oneOf alternatives)
    (reached : ∀ output next,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next [] →
        next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next))
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned)) :
    (send ⟨[(statement, values)]⟩).check post ctx := by
  obtain ⟨output, next, others, step⟩ := modeled
  obtain rfl := runScriptStep_others step
  refine (check_send_single_of_step step (notChoice _ _ _ step)).2 (reached _ _ step ?_)
  exact runScriptStep_valid (profile := Profile.pinned) runContext ctx.clock ctx.index statement values rfl rfl valid
    { output, next } (by rw [step]; simp [RunStep.executions])

/-- For every admitted database and environment: the connection of the fresh start satisfies the validity
condition that the step rules ask of the connection of their context. In plain words, a run that starts from
an admitted database starts valid, and it has no open transaction. Proof sketch: the database of the start is
the admitted database; the start has no snapshot. -/
theorem ExecutionContext.initial_holds_valid (db : Database) (env : Env) :
    (ExecutionContext.initial db env).connection.state.Holds (Database.Valid Profile.pinned) :=
  ⟨db.valid, fun _ same => by simp [ExecutionContext.initial, Database.Raw.connection] at same⟩

end Belay.Sqlite
