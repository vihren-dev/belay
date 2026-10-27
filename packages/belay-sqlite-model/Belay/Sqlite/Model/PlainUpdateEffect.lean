import Belay.Sqlite.Model.PlainDeleteEffect
import Belay.Sqlite.Model.DatabaseLaws
import Belay.Sqlite.Model.StatementStep

set_option doc.verso true

/-!
The effect of one plain UPDATE of the model (ADR 0017, S6). A plain UPDATE is a resolved update
without a RETURNING clause, subqueries or trigger and foreign-key rules. The module shows what the
model's run of such a statement stores: the rows that {lit}`LiteralData.updated` computes, with the
assignments, the generated columns and the stored-value coercions of the model. A universal claim about an
UPDATE then needs only these rows, not the engine.
-/

namespace Belay.Sqlite.Model
open Resolved

/-- For every present table, assignment list, filter, returning list and
subquery list, a successful UPDATE without a foreign-key or trigger plan
stores exactly the rows computed by {name}`LiteralData.updated`. This states
the effect only; it does not assert that the statement passes its support
check or succeeds on every database. Proof sketch: success excludes the
alias-mismatch and constraint-failure branches, leaving the stored row list. -/
theorem runStatement_update_ok (clock : Int) (counters : Counters) (parameters : List Value)
    {database after : Database} {target : Nat} {table : Table}
    (assignments : List (Nat × Expr)) (filter : Option Expr)
    (returning : List (Expr × String)) (subqueries : List Query)
    (present : database.table target = some table)
    (success : (runStatement clock counters parameters
      (.update target assignments filter returning subqueries none) database).effect = .ok after) :
    after = database.setRows target
      (LiteralData.updated (statementContext clock counters parameters database subqueries)
        table assignments filter).rows := by
  simp only [runStatement, present, Option.map_none, StatementRun.withKeys] at success
  split at success
  · cases success
  · unfold checkedWrite at success
    split at success
    · cases success; rfl
    · cases success

/-- Under the successful plain UPDATE assumptions of {name}`runStatement_update_ok`,
if the target has a storage slot, its resulting table is exactly the computed
updated table, including its unchanged schema. Proof sketch: the exact effect
stores those rows, and {name}`Database.table_setRows` identifies the table. -/
theorem table_after_update_ok (clock : Int) (counters : Counters) (parameters : List Value)
    {database after : Database} {target : Nat} {table : Table}
    (assignments : List (Nat × Expr)) (filter : Option Expr)
    (returning : List (Expr × String)) (subqueries : List Query)
    (present : database.table target = some table) (aligned : target < database.rows.length)
    (success : (runStatement clock counters parameters
      (.update target assignments filter returning subqueries none) database).effect = .ok after) :
    after.table target = some
      (LiteralData.updated (statementContext clock counters parameters database subqueries)
        table assignments filter) := by
  rw [runStatement_update_ok clock counters parameters assignments filter returning subqueries present success]
  exact Database.table_setRows _ present aligned

/-- For every connection, plain update and error-free step that continues: the next connection has the
database in which the table at the target holds the rows that {name}`LiteralData.updated` computes. The
statement context is that of the clock value of the step and of the counters that the update reads, with
the values bound to its parameters. Proof sketch: {name}`runScriptStep_effect` gives the effect of the run,
and {name}`runStatement_update_ok` reads the stored rows from a successful effect. -/
theorem plainUpdate_database {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {target : Nat} {assignments : List (Nat × Resolved.Expr)} {filter : Option Resolved.Expr}
    {after : ResolveState} {table : Table}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.update target assignments filter [] [] none, after))
    (present : connection.state.database.table target = some table)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (noError : output.isError = false) :
    ∃ value : Int, statementClock clock index (.update target assignments filter [] [] none) = some value ∧
      next.state.database = connection.state.database.setRows target
        (LiteralData.updated (Resolved.statementContext value
          (connection.state.counters.view
            (Resolved.Statement.update target assignments filter [] [] none).counterReads)
          parameters connection.state.database []) table assignments filter).rows := by
  obtain ⟨value, database, timed, effect, nextEq⟩ :=
    runScriptStep_effect found (by simp [Resolved.Statement.isControl]) step noError
  refine ⟨value, timed, ?_⟩
  simp only [SqlState.statementRun] at effect
  have stored := runStatement_update_ok value
    (connection.state.counters.view (Resolved.Statement.update target assignments filter [] [] none).counterReads)
    parameters assignments filter [] [] present (by
      simpa [runStatement, present, StatementRun.withKeys, Option.map_none] using effect)
  rw [nextEq]
  exact stored

/-- For every clock, statement values, state, run, transition, target and rule fields: the output of a step
of an update is never a choice between results. Proof sketch: as {name}`Output.ofStep_delete_ne_oneOf`;
every case gives a done count, an error or an unmodeled stop. -/
theorem Output.ofStep_update_ne_oneOf (clock : Int) (parameters : List Value) (before : SqlState)
    (run : StatementRun) (transition : SqlTransition) (target : Nat) (assignments filter returning subqueries rules)
    (alternatives : List (List (List Value))) :
    Output.ofStep clock parameters (.update target assignments filter returning subqueries rules) before run
      transition ≠ .oneOf alternatives := by
  unfold Output.ofStep
  rcases haltError transition with _ | failure
  · dsimp only
    split
    · split <;> simp
    · simp
  · cases failure <;> simp

/-- For every connection, statement that resolves to an update, and step that continues: the output of the
step is not a choice between results. Proof sketch: {name}`runScriptStep_ran` gives the output as
{name}`Output.ofStep` of the resolved statement, which {name}`Output.ofStep_update_ne_oneOf` treats. -/
theorem runScriptStep_update_ne_oneOf {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {target : Nat} {assignments : List (Nat × Resolved.Expr)} {filter : Option Resolved.Expr}
    {returning subqueries rules} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.update target assignments filter returning subqueries rules, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (alternatives : List (List (List Value))) : output ≠ .oneOf alternatives := by
  obtain ⟨resolved, later, value, same, -, -, -, outputEq, -⟩ := runScriptStep_ran step
  rw [found] at same
  cases same
  rw [outputEq]
  exact Output.ofStep_update_ne_oneOf _ _ _ _ _ _ _ _ _ _ _ alternatives

end Belay.Sqlite.Model
