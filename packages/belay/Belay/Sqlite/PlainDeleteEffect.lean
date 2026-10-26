import Belay.Sqlite.PlainInsertEffect

set_option doc.verso true

/-!
What a program that sends one plain DELETE checks in a fresh run (ADR 0017, S6). A plain DELETE is a
resolved delete without a RETURNING clause, subqueries or trigger and foreign-key rules; the model
law about what its run stores is {name}`Belay.Sqlite.Model.plainDelete_database`. A universal claim about a
DELETE then needs only the rows that the filter keeps, not the engine.
-/

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every database, environment, plain delete that resolves from the initial connection and is
modeled, and post: a program that sends the delete checks the post at its fresh start when the post
holds for every error-free final context whose connection sees the database in which the target table
keeps the rows that {name}`LiteralData.deleted` keeps, and that database is valid. The premise is about the database
only, so a claim about the rows that the delete keeps needs no engine reasoning. Proof sketch:
{name}`check_send_single_of_step` with the step of the model; {name}`plainDelete_database` gives the
database, {name}`runScriptStep_valid` its validity, and {name}`runScriptStep_delete_ne_oneOf` rules out a
choice. -/
theorem Sql.ifOk_send_plainDelete {db : Database} {env : Env} {statement : Syntax.Statement}
    {values : List Value} {target : Nat} {filter : Option Resolved.Expr} {after : ResolveState}
    {table : Table}
    (found : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.delete target filter [] [] none, after))
    (present : db.raw.table target = some table)
    (modeled : ∃ output next others, runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
      statement values = .continued output next others)
    {post : List Output → ExecutionContext → Prop}
    (reached : ∀ (value : Int) (outputs : List Output) (final : ExecutionContext),
      final.connection.state.database = db.raw.setRows target
        (LiteralData.deleted (Resolved.statementContext value
          ((db.raw.connection env.counters).state.counters.view
            (Resolved.Statement.delete target filter [] [] none).counterReads)
          values db.raw []) table filter).rows →
      final.connection.state.database.Valid Profile.pinned → final.outputs.allOk = true →
      post outputs final) :
    (send ⟨[(statement, values)]⟩).ifOk post (ExecutionContext.initial db env) := by
  obtain ⟨output, next, others, step⟩ := modeled
  refine (check_send_single_of_step (state := ExecutionContext.initial db env) step
    (runScriptStep_delete_ne_oneOf found step)).2 ?_
  intro allOk
  have noError : output.isError = false := by
    simp [ExecutionContext.next, List.allOk] at allOk
    exact allOk.2.1
  obtain ⟨value, -, effect⟩ := plainDelete_database found present step noError
  have start : (db.raw.connection env.counters).state.Holds (Database.Valid Profile.pinned) :=
    ⟨db.valid, fun _ same => by simp [Database.Raw.connection] at same⟩
  have valid : next.state.Holds (Database.Valid Profile.pinned) :=
    runScriptStep_valid (profile := Profile.pinned) runContext env.clock 0 statement values rfl rfl start
      { output, next } (by rw [step]; simp [RunStep.executions])
  exact reached value [output] _ effect valid.1 allOk

end Belay.Sqlite
