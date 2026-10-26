import Belay.Sqlite.SendStepRules
import Belay.Sqlite.PlainDeleteEffect

set_option doc.verso true

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every context in which the connection is valid, plain delete that resolves from the connection and
is modeled, and post: a program that sends the delete checks the post when it holds in the two cases of the
step:

* the delete succeeds: the next connection is {name}`Model.Connection.afterWrite` with the database in which
  the target holds the rows that {name}`LiteralData.deleted` gives, and that connection is valid;
* the delete fails: the next connection is {name}`Model.Connection.afterWrite` with the same database, and that
  connection is valid.

In both cases the output list is the one output of the step, which does not end the run
({name}`Output.endsRun`), and the context is the next context after it.
The counters of the connection are those after the counts of the statement, for the clock value that the
statement reads. Proof sketch: {name}`Sql.check_send_of_step`; {name}`runScriptStep_effect` and
{name}`plainDelete_database` give the connection after a success, and {name}`runScriptStep_plainWrite_failed` after a
failure. -/
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
  refine Sql.check_send_of_step modeled (fun _ _ _ step => runScriptStep_delete_ne_oneOf found step) ?_ valid
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

end Belay.Sqlite
