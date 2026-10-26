import Belay.Sqlite.Model.PlainInsertEffect

set_option doc.verso true

/-!
The effect of one plain DELETE of the model (ADR 0017, S6). A plain DELETE is a resolved delete
without a RETURNING clause, subqueries or trigger and foreign-key rules. The module shows what the
model's run of such a statement stores: the table without the rows that the filter selects. A
universal claim about a DELETE then needs only the filter, not the engine.
-/

namespace Belay.Sqlite.Model

/-- For every connection, plain delete and error-free step that continues: the next connection has the
database in which the table at the target keeps the rows that {name}`LiteralData.deleted` keeps. The
statement context is that of the clock value of the step and of the counters that the delete reads, with
the values bound to its parameters. Proof sketch: {name}`runScriptStep_effect` gives the effect of the
run; the run of a delete without rules is the successful write of the kept rows. -/
theorem plainDelete_database {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {target : Nat} {filter : Option Resolved.Expr} {after : ResolveState} {table : Table}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.delete target filter [] [] none, after))
    (present : connection.state.database.table target = some table)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (noError : output.isError = false) :
    ∃ value : Int, statementClock clock index (.delete target filter [] [] none) = some value ∧
      next.state.database = connection.state.database.setRows target
        (LiteralData.deleted (Resolved.statementContext value
          (connection.state.counters.view (Resolved.Statement.delete target filter [] [] none).counterReads)
          parameters connection.state.database []) table filter).rows := by
  obtain ⟨value, database, timed, effect, nextEq⟩ :=
    runScriptStep_effect found (by simp [Resolved.Statement.isControl]) step noError
  refine ⟨value, timed, ?_⟩
  simp only [SqlState.statementRun, runStatement, present, StatementRun.withKeys, Option.map_none] at effect
  rw [nextEq]
  cases effect
  rfl

/-- For every clock, statement values, state, run, transition, target and rule fields: the output of a step
of a delete is never a choice between results. Proof sketch: as {name}`Output.ofStep_insert_ne_oneOf`;
every case gives a done count, an error or an unmodeled stop. -/
theorem Output.ofStep_delete_ne_oneOf (clock : Int) (parameters : List Value) (before : SqlState)
    (run : StatementRun) (transition : SqlTransition) (target : Nat) (filter returning subqueries rules)
    (alternatives : List (List (List Value))) :
    Output.ofStep clock parameters (.delete target filter returning subqueries rules) before run transition ≠
      .oneOf alternatives := by
  unfold Output.ofStep
  rcases haltError transition with _ | failure
  · dsimp only
    split
    · split <;> simp
    · simp
  · cases failure <;> simp

/-- For every connection, statement that resolves to a delete, and step that continues: the output of the
step is not a choice between results. Proof sketch: {name}`runScriptStep_ran` gives the output as
{name}`Output.ofStep` of the resolved statement, which {name}`Output.ofStep_delete_ne_oneOf` treats. -/
theorem runScriptStep_delete_ne_oneOf {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution} {target : Nat}
    {filter : Option Resolved.Expr} {returning subqueries rules} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.delete target filter returning subqueries rules, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (alternatives : List (List (List Value))) : output ≠ .oneOf alternatives := by
  obtain ⟨resolved, later, value, same, -, -, -, outputEq, -⟩ := runScriptStep_ran step
  rw [found] at same
  cases same
  rw [outputEq]
  exact Output.ofStep_delete_ne_oneOf _ _ _ _ _ _ _ _ _ _ alternatives

end Belay.Sqlite.Model
