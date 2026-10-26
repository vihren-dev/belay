import Belay.Sqlite.ExecutionStep
import Belay.Sqlite.ExecutionSuccess
import Belay.Sqlite.ProgramQueries

set_option doc.verso true

/-!
What a program that sends one plain INSERT checks in a fresh run (ADR 0017, S6). A plain INSERT is a
resolved insert without a RETURNING clause, subqueries or trigger and foreign-key rules; the model
laws about what its run stores are in {lit}`Belay.Sqlite.Model.PlainInsertEffect`. A universal claim
about an INSERT then needs only the rows that the statement adds to the table, not the engine.
-/

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every post, context, statement, values and continuing step whose output is not a choice:
a program that sends the one statement checks the post exactly at the context after the step with
the one output. Proof sketch: {name}`Sql.check_exec` with the step; the output is not a choice, so
only the raw continuation remains. -/
theorem check_send_single_of_step {statement : Syntax.Statement} {values : List Value}
    {post : List Output → ExecutionContext → Prop} {state : ExecutionContext}
    {actual : Output} {connection : Connection} {others : List StatementExecution}
    (step : runScriptStep runContext state.clock state.index state.connection statement values =
      .continued actual connection others)
    (notChoice : ∀ alternatives, actual ≠ .oneOf alternatives) :
    (send ⟨[(statement, values)]⟩).check post state ↔ post [actual] (state.next actual connection) := by
  unfold send
  simp only [sendStatements]
  rw [Sql.check_exec, step]
  dsimp only
  rw [runScriptStep_executions step]
  simp only [List.mem_singleton, forall_eq]
  cases actual with
  | oneOf alternatives => exact absurd rfl (notChoice alternatives)
  | done _ | rows _ | error _ | unmodeled _ =>
    simp [Sql.check_pure, Sql.map]

/-- For every database, environment (no assumption that it is complete), plain insert that resolves
from the initial connection and is modeled, and post: a program that sends the insert checks the
post at its fresh start when the post holds for every error-free final context whose connection
sees the database with the inserted rows, and that database is valid. The rows are those of
{name}`plainInsert_database` for the clock value and the counters of the step. Only the reached
database and its validity enter, so a claim about the rows added by the statement needs no engine
reasoning. Proof sketch: {name}`check_send_single_of_step` with the step of the model;
{name}`plainInsert_database` gives the database, {name}`runScriptStep_valid` its validity, and
{name}`runScriptStep_insert_ne_oneOf` rules out a choice. -/
theorem Sql.ifOk_send_plainInsert {db : Database} {env : Env} {statement : Syntax.Statement}
    {values : List Value} {target : Nat} {cells : List (List Resolved.Cell)} {after : ResolveState}
    {table : Table}
    (found : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.insert target cells [] [] none, after))
    (present : db.raw.table target = some table)
    (modeled : ∃ output next others, runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
      statement values = .continued output next others)
    {post : List Output → ExecutionContext → Prop}
    (reached : ∀ (value : Int) (outputs : List Output) (final : ExecutionContext),
      final.connection.state.database = db.raw.setRows target
        (LiteralData.inserted table (Resolved.rowsAt (Resolved.statementContext value
          ((db.raw.connection env.counters).state.counters.view
            (Resolved.Statement.insert target cells [] [] none).counterReads)
          values db.raw []) table.shape.columns cells)).rows →
      final.connection.state.database.Valid Profile.pinned → final.outputs.allOk = true →
      post outputs final) :
    (send ⟨[(statement, values)]⟩).ifOk post (ExecutionContext.initial db env) := by
  obtain ⟨output, next, others, step⟩ := modeled
  refine (check_send_single_of_step (state := ExecutionContext.initial db env) step
    (runScriptStep_insert_ne_oneOf found step)).2 ?_
  intro allOk
  have noError : output.isError = false := by
    simp [ExecutionContext.next, List.allOk] at allOk
    exact allOk.2.1
  obtain ⟨value, -, effect⟩ := plainInsert_database found present step noError
  have start : (db.raw.connection env.counters).state.Holds (Database.Valid Profile.pinned) :=
    ⟨db.valid, fun _ same => by simp [Database.Raw.connection] at same⟩
  have valid : next.state.Holds (Database.Valid Profile.pinned) :=
    runScriptStep_valid (profile := Profile.pinned) runContext env.clock 0 statement values rfl rfl start
      { output, next } (by rw [step]; simp [RunStep.executions])
  exact reached value [output] _ effect valid.1 allOk

end Belay.Sqlite
