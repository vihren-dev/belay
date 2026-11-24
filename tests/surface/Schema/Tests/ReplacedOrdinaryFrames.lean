import Belay

set_option doc.verso true

/-! A fixture of {lit}`tests/surface_schema_script_test.py`. The original nonquery error and
state frames, and the two conditional creation equations, follow from the retained model tools. -/

namespace Belay.Sqlite.ReplacedOrdinaryFrames
open Belay.Sqlite.Model

/-- For every step that continues, of a statement that resolves to a statement other than a query, if the
transition of the run does not halt for any clock value, the output of the step is no error. Proof sketch: the
output is {name}`Output.ofStep` of the run ({name}`runScriptStep_continued_spec`), and
{name}`Output.ofStep_isError_of_noHalt` reads it. -/
theorem runScriptStep_isError_false {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {others : List StatementExecution} {resolved : Resolved.Statement} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (notQuery : ∀ query subqueries, resolved ≠ .query query subqueries)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (quiet : ∀ value, haltError (advanceRun index resolved connection.state
      (connection.state.statementRun value parameters resolved)) = none) :
    output.isError = false := by
  obtain ⟨resolved', after', value, same, -, -, -, ofStep, -⟩ := runScriptStep_continued_spec step
  rw [found] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
  rw [← ofStep]
  exact Output.ofStep_isError_of_noHalt _ _ _ _ _ _ _ notQuery (quiet value)

/-- For every connection, ordinary statement that is no query, and continuing step: if each error of
the run of the statement has the reason {name}`ExecutionError.unmodeled`, then the step has no error
output, the effect of the run succeeds with a database, and the next connection is the connection with
that database and the counters after the counts of the run. In plain words, a statement that can fail
only by being outside the model never fails in the model: it ends the run or it succeeds. Proof sketch:
an effect that fails publishes its reason, so the output is {name}`Output.unmodeled`, which ends the
run, and a continuing step does not end it ({name}`runScriptStep_continued`); so the effect succeeds,
which has no error output ({name}`Output.ofStep_isError_of_noHalt`), and
{name}`runScriptStep_effect` reads the next connection. -/
theorem runScriptStep_effect_of_unmodeled {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {resolved : Resolved.Statement} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (ordinary : resolved.isControl = false)
    (notQuery : ∀ query subqueries, resolved ≠ .query query subqueries)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (unmodeled : ∀ value reason reached,
      (connection.state.statementRun value parameters resolved).effect = .error (reason, reached) →
        reason = .unmodeled) :
    output.isError = false ∧ ∃ value database,
      statementClock clock index resolved = some value ∧
      (connection.state.statementRun value parameters resolved).effect = .ok database ∧
      next = { connection with state := { connection.state with
        database := database
        counters := connection.state.counters.apply
          (connection.state.statementRun value parameters resolved).counts } } := by
  obtain ⟨resolved', after', value, same, -, -, -, ofStep, endsRun, -, -⟩ := runScriptStep_continued_spec step
  rw [found] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
  rw [advanceRun_ordinary index resolved connection.state _ ordinary] at ofStep
  cases effect : (connection.state.statementRun value parameters resolved).effect with
  | error failure =>
    exfalso
    obtain ⟨reason, reached⟩ := failure
    have reasonEq := unmodeled value reason reached effect
    have halted (outcome : Outcome) : haltError (.halt outcome) = outcome.error? := by
      cases outcome <;> rfl
    have error : haltError ((connection.state.publish index (.error (reason, reached))).counted
        (connection.state.statementRun value parameters resolved).counts) = some reason := by
      simp only [SqlState.publish, SqlTransition.counted, halted]
      exact connection.state.failed_error ..
    rw [effect] at ofStep
    subst reasonEq
    simp only [Output.ofStep, error] at ofStep
    subst ofStep
    simp [Output.endsRun] at endsRun
  | ok database =>
    have noError : output.isError = false := by
      rw [← ofStep, effect, Output.ofStep_isError_of_noHalt _ _ _ _ _ _ _ notQuery (by
        simp [SqlTransition.counted, SqlState.publish, haltError])]
    exact ⟨noError, runScriptStep_effect found ordinary step noError⟩

/-- For every connection, statement that resolves to an ordinary resolved statement (not a transaction
control), error-free step that continues, and database that is the next database: the next connection is
the connection with that database and some counters. In plain words, the clock, the snapshot and both
connection settings stay as they were. Proof sketch: {name}`runScriptStep_effect` gives the next
connection with the database of the effect; the premise identifies that database. -/
theorem runScriptStep_next_of_database {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {resolved : Resolved.Statement} {after : ResolveState} {database : Model.Database}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (ordinary : resolved.isControl = false)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (noError : output.isError = false) (stored : next.state.database = database) :
    ∃ counters, next = { connection with state := { connection.state with database, counters } } := by
  obtain ⟨value, effect, -, -, nextEq⟩ := runScriptStep_effect found ordinary step noError
  rw [nextEq] at stored
  exact ⟨_, by rw [nextEq, ← stored]⟩

/-- For every context, clock, statement index, connection, CREATE TABLE and bound values: if
no table or view has the name, or the name is reserved ({name}`createTableKept` is false),
then one step of the statement with {lit}`IF NOT EXISTS` is the step without it. Proof
sketch: both resolve with {name}`resolveCreateTable`. -/
theorem runScriptStep_createTable_ifNotExists_free {context : ResolveContext} {clock : Option Clock}
    {index : Nat} {connection : Connection} {name : Identifier} {columns : List Syntax.ColumnDefinition}
    {constraints : List Syntax.TableConstraint} {options : Syntax.TableOptions} {parameters : List Value}
    (free : createTableKept connection.state.database.catalog name = false) :
    runScriptStep context clock index connection (.createTable name columns constraints options true) parameters =
      runScriptStep context clock index connection (.createTable name columns constraints options) parameters :=
  runScriptStep_congr_resolve (by
    simp [statement_arms, resolveCreateTableIf, Connection.resolveState, free])

/-- For every context, clock, statement index, connection, CREATE INDEX and bound values: if
{name}`createIndexKept` is false (the table is missing, a name is reserved, or no index has
the name), then one step of the statement with {lit}`IF NOT EXISTS` is the step without it.
Proof sketch: both resolve with {name}`resolveCreateIndex`. -/
theorem runScriptStep_createIndex_ifNotExists_free {context : ResolveContext} {clock : Option Clock}
    {index : Nat} {connection : Connection} {name tableName : Identifier} {unique : Bool}
    {terms : List Syntax.OrderTerm} {filter : Option Syntax.Expr} {parameters : List Value}
    (free : createIndexKept connection.state.database.catalog name tableName = false) :
    runScriptStep context clock index connection (.createIndex name unique tableName terms filter true) parameters =
      runScriptStep context clock index connection (.createIndex name unique tableName terms filter) parameters :=
  runScriptStep_congr_resolve (by
    simp [statement_arms, resolveCreateIndexIf, Connection.resolveState, free])

#print axioms runScriptStep_isError_false
#print axioms runScriptStep_effect_of_unmodeled
#print axioms runScriptStep_next_of_database
#print axioms runScriptStep_createTable_ifNotExists_free
#print axioms runScriptStep_createIndex_ifNotExists_free

end Belay.Sqlite.ReplacedOrdinaryFrames
