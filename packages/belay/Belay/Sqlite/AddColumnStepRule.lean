import Belay.Sqlite.SendStepRules
import Belay.Sqlite.AddColumnEffect

set_option doc.verso true

/-! The rule for one sent ADD COLUMN at any context (ADR 0017, S6): the premises that a proof of a program
needs, and nothing about the other statements of the program. -/

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every context {lit}`ctx`, statement, values and post, with a valid connection in {lit}`ctx`: the program
that sends the statement checks the post at {lit}`ctx` if these premises hold.

* {lit}`found`: the statement resolves from the connection of {lit}`ctx` to an ADD COLUMN on position {lit}`target`.
* {lit}`present`: that position holds a table.
* {lit}`modeled`: the model runs the statement at {lit}`ctx` to a step that continues.
* {lit}`success`: for every output that is not an error and does not end the run ({name}`Output.endsRun`), for
  every clock value that the statement reads at the index of {lit}`ctx`, for every default value that is NULL when
  the column default reads the clock and is the value that {name}`readDefaultValue` reads otherwise, and for every
  connection that is {name}`Model.Connection.afterWrite` with the database that has the column appended with the
  default in every row, and with the counts of the statement for that clock value: if that connection is
  valid, the post holds for the list of that one output and the context after it.
* {lit}`failure`: for every output that is an error and does not end the run, for every integer taken as the clock
  value, and for every connection that is {name}`Model.Connection.afterWrite` with the unchanged database and the
  counts of the statement for that value: if that connection is valid, the post holds for the list of that
  one output and the context after it. The premise does not tie the integer to the clock.

Proof sketch: {name}`Sql.check_send_of_step`; {name}`runScriptStep_effect` and {name}`addColumn_database` give the
connection after a success, and {name}`runScriptStep_addColumn_failed` gives it after a refusal. -/
theorem Sql.check_send_addColumn {ctx : ExecutionContext} {statement : Syntax.Statement}
    {values : List Value} {target : Nat} {column : CatalogColumn} {refusesPopulated : Bool}
    {after : ResolveState} {table : Table} {post : List Output → ExecutionContext → Prop}
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState statement =
      .ok (.addColumn target column refusesPopulated, after))
    (present : ctx.connection.state.database.table target = some table)
    (modeled : ∃ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others)
    (success : ∀ (output : Output) (value : Int) (default : Value) (next : Connection), output.isError = false → output.endsRun = false →
      statementClock ctx.clock ctx.index (.addColumn target column refusesPopulated) = some value →
      (column.clockDefault = true → default = .null) →
      (column.clockDefault = false → readDefaultValue column = .ok default) →
      next = ctx.connection.afterWrite (ctx.connection.state.database.addColumn target column default)
        (ctx.connection.state.statementRun value values (.addColumn target column refusesPopulated)).counts →
      next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next))
    (failure : ∀ (output : Output) (value : Int) (next : Connection), output.isError = true → output.endsRun = false →
      next = ctx.connection.afterWrite ctx.connection.state.database
        (ctx.connection.state.statementRun value values (.addColumn target column refusesPopulated)).counts →
      next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next)) :
    (send ⟨[(statement, values)]⟩).check post ctx := by
  refine Sql.check_send_of_step (fun _ _ resolved => by
      obtain rfl := (Prod.mk.inj (Except.ok.inj (resolved.symm.trans found))).1
      rfl) modeled
    (fun _ _ _ step => runScriptStep_ne_oneOf_of_not_query found (by intro _ _ same; cases same) step) ?_ valid
  intro output next step' hvalid
  have ends := (runScriptStep_continued step').2
  cases noError : output.isError
  · obtain ⟨value, database, timed, effect, nextEq⟩ :=
      runScriptStep_effect found (by simp [Resolved.Statement.isControl]) step' noError
    obtain ⟨default, clockNull, clockRead, dbEq⟩ := addColumn_database found present step' noError
    subst nextEq
    simp only at dbEq
    subst dbEq
    exact success output value default _ noError ends timed clockNull clockRead rfl hvalid
  · obtain ⟨value, rfl⟩ := runScriptStep_addColumn_failed found step' noError
    exact failure output value _ noError ends rfl hvalid

end Belay.Sqlite
