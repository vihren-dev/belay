import Belay.Sqlite.SendStepRules
import Belay.Sqlite.SingleStatementChecks
import Belay.Sqlite.ExecutionSpecifications

set_option doc.verso true

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every context, script of one SELECT statement and post: a program that reads the single value of the
script checks the post when the step of the statement continues, and the post holds for every output that
SQLite may select from the output of the step. The reached context is the context after the step with the
selected output, and its connection is the connection of the start: a SELECT changes nothing, also when it
fails. The value is {name}`singleValue` of the selected result, so it is {lean}`(none : Option Value)` when the
query fails or does not give exactly one value. Proof sketch: {name}`check_single_of_statement` for the
step; {name}`runScriptStep_select_keeps` gives the connection and that there is no other execution, and the
execution of the step is its own. -/
theorem Sql.check_single_select {ctx : ExecutionContext} {script : Script}
    {one : script.statements.length = 1} {statement : Syntax.Statement} {values : List Value}
    {columns source joins filter groupBy orderBy limit offset subqueries having distinct compound}
    {post : Option Value → ExecutionContext → Prop}
    (isStatement : script.statements = [(statement, values)])
    (isSelect : statement =
      .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound)
    (modeled : ∃ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others)
    (reached : ∀ selected : Output,
      OutputChoice (runScriptStep runContext ctx.clock ctx.index ctx.connection statement values).output selected →
        post (singleValue (queryResult selected)) (ctx.next selected ctx.connection)) :
    (single script one).check post ctx := by
  refine (check_single_of_statement script one isStatement post ctx).2 ?_
  obtain ⟨output, next, others, step⟩ := modeled
  rw [step]
  obtain ⟨rfl, rfl⟩ := runScriptStep_select_keeps (isSelect ▸ step)
  intro found member selected choice
  obtain rfl := Sql.Branch.found_eq step member
  exact reached selected (by rw [step]; exact choice)

/-- For every context, script of one SELECT statement and post: a program that reads the rows of the script
checks the post when the step continues, and the post holds for every output that SQLite may select from the
output of the step, with the context after the step and the connection of the start. The value is
{name}`queryResult` of the selected output. Proof sketch: {name}`check_query` for the step, and
{name}`runScriptStep_select_keeps` as for {name}`Sql.check_single_select`. -/
theorem Sql.check_query_select {ctx : ExecutionContext} {script : Script}
    {one : script.statements.length = 1} {statement : Syntax.Statement} {values : List Value}
    {columns source joins filter groupBy orderBy limit offset subqueries having distinct compound}
    {post : Except Nat (List (List Value)) → ExecutionContext → Prop}
    (isStatement : script.statements = [(statement, values)])
    (isSelect : statement =
      .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound)
    (modeled : ∃ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others)
    (reached : ∀ selected : Output,
      OutputChoice (runScriptStep runContext ctx.clock ctx.index ctx.connection statement values).output selected →
        post (queryResult selected) (ctx.next selected ctx.connection)) :
    (query script one).check post ctx := by
  rw [check_query]
  obtain ⟨output, next, others, step⟩ := modeled
  obtain rfl : script = ⟨[(statement, values)]⟩ := by cases script; simp_all
  simp only [List.getElem_cons_zero]
  rw [step]
  obtain ⟨rfl, rfl⟩ := runScriptStep_select_keeps (isSelect ▸ step)
  intro found member selected choice
  obtain rfl := Sql.Branch.found_eq step member
  exact reached selected (by rw [step]; exact choice)

/-- For every context, SELECT statement with its values, and post: a program that sends the statement checks the
post when the step of the statement continues, and the post holds for every output that SQLite may select from
the output of the step. The output list is the selected output alone, the reached context is the context after
the step with that output, and its connection is the connection of the start. In plain words, this rule covers a
sent read whose result is a choice between results. Proof sketch: {name}`Sql.check_continued` for the step;
{name}`runScriptStep_select_keeps` gives the connection and that there is no other execution; the rest of the
program is pure. -/
theorem Sql.check_send_select {ctx : ExecutionContext} {statement : Syntax.Statement} {values : List Value}
    {columns source joins filter groupBy orderBy limit offset subqueries having distinct compound}
    {post : List Output → ExecutionContext → Prop}
    (isSelect : statement =
      .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound)
    (modeled : ∃ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others)
    (reached : ∀ selected : Output,
      OutputChoice (runScriptStep runContext ctx.clock ctx.index ctx.connection statement values).output selected →
        post [selected] (ctx.next selected ctx.connection)) :
    (send ⟨[(statement, values)]⟩).check post ctx := by
  obtain ⟨output, next, others, step⟩ := modeled
  obtain ⟨rfl, rfl⟩ := runScriptStep_select_keeps (isSelect ▸ step)
  unfold send
  simp only [sendStatements]
  rw [Sql.check_continued step]
  intro found member selected choice
  obtain rfl := Sql.Branch.found_eq step member
  simp only [Sql.check_map, Sql.check_pure]
  exact reached selected (by rw [step]; exact choice)

end Belay.Sqlite
