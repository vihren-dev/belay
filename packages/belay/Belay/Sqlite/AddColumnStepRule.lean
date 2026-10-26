import Belay.Sqlite.SendStepRules
import Belay.Sqlite.AddColumnEffect

set_option doc.verso true

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every context in which the connection is valid, ADD COLUMN that resolves from the connection and is
modeled, and post: a program that sends the statement checks the post when it holds in the two cases of the
step:

* the statement succeeds: the next connection is {name}`Model.Connection.afterWrite` with the database that has
  the column appended and a default value in every row, and that connection is valid. The default value is
  NULL when the default reads the clock, and the value that {name}`readDefaultValue` reads otherwise;
* the statement is refused: the next connection is {name}`Model.Connection.afterWrite` with the same database,
  and that connection is valid.

In both cases the output list is the one output of the step, which does not end the run
({name}`Output.endsRun`), and the context is the next context after it.
The counters of the connection are those after the counts of the statement, for the clock value that the
statement reads. Proof sketch: {name}`Sql.check_send_of_step`; {name}`runScriptStep_effect` and
{name}`addColumn_database` give the connection after a success, and {name}`runScriptStep_addColumn_failed`
after a refusal. -/
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
  refine Sql.check_send_of_step modeled
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
