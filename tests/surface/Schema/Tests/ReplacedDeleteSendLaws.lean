import ReplacedPlainWriteLaws

set_option doc.verso true

/-! A temporary retention test for ADR 0033, slice 2. It proves
the two former DELETE send rules using the DELETE database-effect witness with the original premises. -/

namespace Belay.Sqlite.ReplacedPlainWriteLaws
open Belay.Sqlite Model Model.ReplacedPlainWriteLaws

/-- The deleted law {lit}`Sql.ifOk_send_plainDelete`. For every database, environment, plain delete that resolves from the initial connection and is
modeled, and post: a program that sends the delete checks the post at its fresh start when the post
holds for every error-free final context whose connection sees the database in which the target table
keeps the rows that {name}`LiteralData.deleted` keeps, and that database is valid. The premise is about the database
only, so a claim about the rows that the delete keeps needs no engine reasoning. Proof sketch:
{name}`check_send_single_of_step` with the step of the model; {name}`plainDelete_database` gives the
database, {name}`runScriptStep_valid` its validity, and {name}`runScriptStep_ne_oneOf_of_not_query` rules out a
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
    (fun _ _ resolved => by
      obtain rfl := (Prod.mk.inj (Except.ok.inj (resolved.symm.trans found))).1
      rfl)
    (runScriptStep_ne_oneOf_of_not_query found (fun _ _ eq => by cases eq) step)).2 ?_
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

/-- The deleted law {lit}`Sql.check_send_plainDelete`. For every context {lit}`ctx`, statement, values and post, with a valid connection in {lit}`ctx`: the program
that sends the statement checks the post at {lit}`ctx` if these premises hold.

* {lit}`found`: the statement resolves from the connection of {lit}`ctx` to a plain delete on position {lit}`target`.
* {lit}`present`: that position holds a table.
* {lit}`modeled`: the model runs the statement at {lit}`ctx` to a step that continues.
* {lit}`success`: for every output that is not an error and does not end the run ({name}`Output.endsRun`), for
  every clock value that the statement reads at the index of {lit}`ctx`, and for every connection that is
  {name}`Model.Connection.afterWrite` with the database in which the target holds the rows that {name}`LiteralData.deleted` gives, and with the
  counts of the statement for that clock value: if that connection is valid, the post holds for the list of that
  one output and the context after it.
* {lit}`failure`: for every output that is an error and does not end the run, for every integer taken as the clock
  value, and for every connection that is {name}`Model.Connection.afterWrite` with the unchanged database and the
  counts of the statement for that value: if that connection is valid, the post holds for the list of that
  one output and the context after it. The premise does not tie the integer to the clock, so a proof of it
  cannot use the clock.

Proof sketch: {name}`Sql.check_send_of_step`; {name}`runScriptStep_effect` and {name}`plainDelete_database` give the connection
after a success, and {name}`runScriptStep_plainWrite_failed` gives it after a failure. -/
theorem Sql.check_send_plainDelete {ctx : ExecutionContext} {statement : Syntax.Statement}
    {values : List Value} {target : Nat} {filter : Option Resolved.Expr} {after : ResolveState}
    {table : Table} {post : List Output → ExecutionContext → Prop}
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState statement =
      .ok (.delete target filter [] [] none, after))
    (present : ctx.connection.state.database.table target = some table)
    (modeled : ∃ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others)
    (success : ∀ (output : Output) (value : Int) (next : Connection), output.isError = false → output.endsRun = false →
      statementClock ctx.clock ctx.index (.delete target filter [] [] none) = some value →
      next = ctx.connection.afterWrite (ctx.connection.state.database.setRows target
        (LiteralData.deleted (Resolved.statementContext value
          (ctx.connection.state.counters.view (Resolved.Statement.delete target filter [] [] none).counterReads)
          values ctx.connection.state.database []) table filter).rows)
        (ctx.connection.state.statementRun value values (.delete target filter [] [] none)).counts →
      next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next))
    (failure : ∀ (output : Output) (value : Int) (next : Connection), output.isError = true → output.endsRun = false →
      next = ctx.connection.afterWrite ctx.connection.state.database
        (ctx.connection.state.statementRun value values (.delete target filter [] [] none)).counts →
      next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next)) :
    (send ⟨[(statement, values)]⟩).check post ctx := by
  refine Sql.check_send_of_step (fun _ _ resolved => by
      obtain rfl := (Prod.mk.inj (Except.ok.inj (resolved.symm.trans found))).1
      rfl) modeled (fun _ _ _ step => runScriptStep_ne_oneOf_of_not_query found (fun _ _ eq => by cases eq) step) ?_ valid
  intro output next step' hvalid
  have ends := (runScriptStep_continued step').2
  cases noError : output.isError
  · obtain ⟨value, database, timed, effect, nextEq⟩ :=
      runScriptStep_effect found (by simp [Resolved.Statement.isControl]) step' noError
    obtain ⟨value', timed', dbEq⟩ := plainDelete_database found present step' noError
    obtain rfl : value' = value := Option.some.inj (timed'.symm.trans timed)
    subst nextEq
    simp only at dbEq
    subst dbEq
    exact success output value' _ noError ends timed' rfl hvalid
  · obtain ⟨value, rfl⟩ := runScriptStep_plainWrite_failed found rfl step' noError
    exact failure output value _ noError ends rfl hvalid

#print axioms Sql.ifOk_send_plainDelete
#print axioms Sql.check_send_plainDelete

end Belay.Sqlite.ReplacedPlainWriteLaws
