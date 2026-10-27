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

/-- For every context, statement, values and post: a program that sends the one statement checks the post when
all of these hold.
- The statement resolves, at the connection of the context, to no INSERT from a query without rules (premise
  {lit}`single`).
- The step of the statement continues at the context (premise {lit}`modeled`).
- No continuing step of the statement has a choice as output (premise {lit}`notChoice`).
- The state of the connection of the context holds {name}`SqlState.Holds` for {lean}`Database.Valid Profile.pinned`
  (premise {lit}`valid`): its database is valid, and its snapshot is valid when it has one. A state without a
  snapshot requires nothing of the snapshot.
- For every output and next connection of a step that continues with no further execution, when the state of
  the next connection holds {name}`SqlState.Holds` for {lean}`Database.Valid Profile.pinned` (the same two
  requirements), the post holds for the one output at the context after the step (premise {lit}`reached`).
In plain words, this rule turns the check of a send into a claim about the connection that the step reaches; the
claim is only about steps from a start and to an end that hold the validity condition. Proof sketch:
{name}`check_send_single_of_step` for the step, with the choice excluded by the premise. -/
theorem Sql.check_send_of_step {ctx : ExecutionContext} {statement : Syntax.Statement} {values : List Value}
    {post : List Output → ExecutionContext → Prop}
    (single : ∀ resolved after, resolveStatement runContext ctx.connection.resolveState statement =
      .ok (resolved, after) → resolved.fromQuery = false)
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
  obtain rfl := runScriptStep_others_of_single step single
  refine (check_send_single_of_step step single (notChoice _ _ _ step)).2 (reached _ _ step ?_)
  exact runScriptStep_valid (profile := Profile.pinned) runContext ctx.clock ctx.index statement values rfl rfl valid
    { output, next } (by rw [step]; simp [RunStep.executions])

/-- For every context, statement that is no INSERT from a query ({name}`Syntax.Statement.isInsertSelect`),
values and post: the check of the send of the statement holds when the premises {lit}`modeled`,
{lit}`notChoice`, {lit}`valid` and {lit}`reached` of {name}`Sql.check_send_of_step` hold. They have the same
quantifiers and the same validity conditions as there. In plain words, a statement that is not written as INSERT
from a query has one execution, so the premise about the resolved statement is not needed. Proof sketch:
{name}`resolveStatement_single` gives the premise {lit}`single` of {name}`Sql.check_send_of_step`. -/
theorem Sql.check_send_of_step_notInsertSelect {ctx : ExecutionContext} {statement : Syntax.Statement}
    {values : List Value} {post : List Output → ExecutionContext → Prop}
    (notInsertSelect : statement.isInsertSelect = false)
    (modeled : ∃ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others)
    (notChoice : ∀ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others →
        ∀ alternatives, output ≠ .oneOf alternatives)
    (reached : ∀ output next,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next [] →
        next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next))
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned)) :
    (send ⟨[(statement, values)]⟩).check post ctx :=
  Sql.check_send_of_step (fun _ _ found => resolveStatement_single _ _ _ _ _ notInsertSelect found)
    modeled notChoice reached valid

/-- For every admitted database and environment: the connection of the fresh start satisfies the validity
condition that the step rules ask of the connection of their context. In plain words, a run that starts from
an admitted database starts valid, and it has no open transaction. Proof sketch: the database of the start is
the admitted database; the start has no snapshot. -/
theorem ExecutionContext.initial_holds_valid (db : Database) (env : Env) :
    (ExecutionContext.initial db env).connection.state.Holds (Database.Valid Profile.pinned) :=
  ⟨db.valid, fun _ same => by simp [ExecutionContext.initial, Database.Raw.connection] at same⟩

end Belay.Sqlite
