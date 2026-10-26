import Belay.Sqlite.SendStepRules
import Belay.Sqlite.PlainDeleteEffect

set_option doc.verso true

/-! The rule for one sent plain delete at any context (ADR 0017, S6): the premises that a proof of a program
needs, and nothing about the other statements of the program. -/

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every context {lit}`ctx`, statement, values and post, with a valid connection in {lit}`ctx`: the program
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
