import Belay.Sqlite.PlainDeleteEffect

set_option doc.verso true

/-!
What a program that sends one plain UPDATE checks in a fresh run (ADR 0017, S6). A plain UPDATE is a
resolved update without a RETURNING clause, subqueries or trigger and foreign-key rules; the model law
about what its run stores is {name}`Belay.Sqlite.Model.plainUpdate_database`. A universal claim about an
UPDATE then needs only the rows that {name}`Belay.Sqlite.Model.LiteralData.updated` computes, not the
engine.
-/

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every database, environment, plain update that resolves from the initial connection and is
modeled, and post: a program that sends the update checks the post at its fresh start when the post
holds for every error-free final context whose connection sees the database in which the target table
holds the rows that {name}`LiteralData.updated` computes, and that database is valid. In plain words, to
prove a claim about the table after an UPDATE, it is enough to prove it for the rows that the assignments
and the filter produce; a failed update, a refused statement and every other final database are outside the
premise. The premise is about the database only, so the claim needs no engine reasoning. Proof sketch:
{name}`check_send_single_of_step` with the step of the model; {name}`plainUpdate_database` gives the
database, {name}`runScriptStep_valid` its validity, and {name}`runScriptStep_update_ne_oneOf` rules out a
choice. -/
theorem Sql.ifOk_send_plainUpdate {db : Database} {env : Env} {statement : Syntax.Statement}
    {values : List Value} {target : Nat} {assignments : List (Nat × Resolved.Expr)}
    {filter : Option Resolved.Expr} {after : ResolveState} {table : Table}
    (found : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.update target assignments filter [] [] none, after))
    (present : db.raw.table target = some table)
    (modeled : ∃ output next others, runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
      statement values = .continued output next others)
    {post : List Output → ExecutionContext → Prop}
    (reached : ∀ (value : Int) (outputs : List Output) (final : ExecutionContext),
      final.connection.state.database = db.raw.setRows target
        (LiteralData.updated (Resolved.statementContext value
          ((db.raw.connection env.counters).state.counters.view
            (Resolved.Statement.update target assignments filter [] [] none).counterReads)
          values db.raw []) table assignments filter).rows →
      final.connection.state.database.Valid Profile.pinned → final.outputs.allOk = true →
      post outputs final) :
    (send ⟨[(statement, values)]⟩).ifOk post (ExecutionContext.initial db env) := by
  obtain ⟨output, next, others, step⟩ := modeled
  refine (check_send_single_of_step (state := ExecutionContext.initial db env) step
    (runScriptStep_update_ne_oneOf found step)).2 ?_
  intro allOk
  have noError : output.isError = false := by
    simp [ExecutionContext.next, List.allOk] at allOk
    exact allOk.2.1
  obtain ⟨value, -, effect⟩ := plainUpdate_database found present step noError
  have start : (db.raw.connection env.counters).state.Holds (Database.Valid Profile.pinned) :=
    ⟨db.valid, fun _ same => by simp [Database.Raw.connection] at same⟩
  have valid : next.state.Holds (Database.Valid Profile.pinned) :=
    runScriptStep_valid (profile := Profile.pinned) runContext env.clock 0 statement values rfl rfl start
      { output, next } (by rw [step]; simp [RunStep.executions])
  exact reached value [output] _ effect valid.1 allOk

end Belay.Sqlite
