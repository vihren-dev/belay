import Belay.Sqlite.PlainUpdateEffect

set_option doc.verso true

/-!
What a program that sends one ADD COLUMN checks in a fresh run (ADR 0017, S6). The model law about what
its run stores is {name}`Belay.Sqlite.Model.addColumn_database`. A claim about a migration that adds a
column then needs only the column and its default value, not the engine.
-/

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every database, environment, ADD COLUMN that resolves from the initial connection and is
modeled, and post: a program that sends the statement checks the post at its fresh start when the post
holds for every error-free final context whose connection sees the database with the column appended and a
default value in every row, and that database is valid. The default value is NULL when the default reads the
clock, and the value that {name}`readDefaultValue` reads otherwise. In plain words, to prove a claim about
the table after an ADD COLUMN, it is enough to prove it for the database with the new column and its
default in every old row; a refused ADD COLUMN is outside the premise. Proof sketch:
{name}`check_send_single_of_step` with the step of the model; {name}`addColumn_database` gives the database,
{name}`runScriptStep_valid` its validity, and {name}`runScriptStep_ne_oneOf_of_not_query` rules out a
choice. -/
theorem Sql.ifOk_send_addColumn {db : Database} {env : Env} {statement : Syntax.Statement}
    {values : List Value} {target : Nat} {column : CatalogColumn} {refusesPopulated : Bool}
    {after : ResolveState} {table : Table}
    (found : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.addColumn target column refusesPopulated, after))
    (present : db.raw.table target = some table)
    (modeled : ∃ output next others, runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
      statement values = .continued output next others)
    {post : List Output → ExecutionContext → Prop}
    (reached : ∀ (value : Value) (outputs : List Output) (final : ExecutionContext),
      (column.clockDefault = true → value = .null) →
      (column.clockDefault = false → readDefaultValue column = .ok value) →
      final.connection.state.database = db.raw.addColumn target column value →
      final.connection.state.database.Valid Profile.pinned → final.outputs.allOk = true →
      post outputs final) :
    (send ⟨[(statement, values)]⟩).ifOk post (ExecutionContext.initial db env) := by
  obtain ⟨output, next, others, step⟩ := modeled
  refine (check_send_single_of_step (state := ExecutionContext.initial db env) step
    (fun _ _ resolved => by
      obtain rfl := (Prod.mk.inj (Except.ok.inj (resolved.symm.trans found))).1
      rfl)
    (runScriptStep_ne_oneOf_of_not_query found (by intro _ _ same; cases same) step)).2 ?_
  intro allOk
  have noError : output.isError = false := by
    simp [ExecutionContext.next, List.allOk] at allOk
    exact allOk.2.1
  obtain ⟨value, clockNull, clockRead, effect⟩ := addColumn_database found present step noError
  have start : (db.raw.connection env.counters).state.Holds (Database.Valid Profile.pinned) :=
    ⟨db.valid, fun _ same => by simp [Database.Raw.connection] at same⟩
  have valid : next.state.Holds (Database.Valid Profile.pinned) :=
    runScriptStep_valid (profile := Profile.pinned) runContext env.clock 0 statement values rfl rfl start
      { output, next } (by rw [step]; simp [RunStep.executions])
  exact reached value [output] _ clockNull clockRead effect valid.1 allOk

end Belay.Sqlite
