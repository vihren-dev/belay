import Belay.Sqlite.Model.PlainWriteFrame

set_option doc.verso true

/-!
What one read-only statement of the model leaves unchanged (ADR 0017, S6). A query, or a statement that
SQLite refuses with a prepare error, writes no row and counts no change. A step of it, whether it gives
rows or an error, ends at the connection where it began. A frame claim about a program with reads then
needs no reasoning about the reads.
-/

namespace Belay.Sqlite.Model

/-- For every query or prepare error, clock value, counters, parameters and database: the effect of its run is
the database itself, or an error with a reason that is not {name}`ExecutionError.constraintFail` or
{name}`ExecutionError.constraintRollback`. Proof sketch: a query's effect is {name}`queryEffect`, which
gives the database or one of three query errors; a prepare error gives its own error. -/
theorem runStatement_readOnly_effect {statement : Resolved.Statement}
    (readOnly : (∃ query subqueries, statement = .query query subqueries) ∨ ∃ error, statement = .prepareError error)
    (clock : Int) (counters : Counters) (parameters : List Value) (database : Database) :
    (∀ after, (runStatement clock counters parameters statement database).effect = .ok after → after = database) ∧
    (∀ reason reached, (runStatement clock counters parameters statement database).effect = .error (reason, reached) →
      reason ≠ .constraintFail ∧ reason ≠ .constraintRollback) := by
  rcases readOnly with ⟨query, subqueries, rfl⟩ | ⟨error, rfl⟩
  · simp only [runStatement, queryEffect]
    split
    · repeat' split
      all_goals simp
    · simp
  · simp [runStatement, step]

/-- For every connection, statement that resolves to a query or a prepare error, and step that continues:
the step has no other execution than the model's own, and the next connection is the connection. In plain
words, a read-only statement changes nothing, also when it fails, and also not the counters: a query
counts no change. Proof sketch: as {name}`runScriptStep_plainWrite_frame`, with
{name}`runStatement_readOnly_effect` for the effect; the run of a read-only statement has no counts, so
{name}`Counters.apply_default` leaves the counters. -/
theorem runScriptStep_readOnly_keeps {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {resolved : Resolved.Statement} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (readOnly : (∃ query subqueries, resolved = .query query subqueries) ∨ ∃ error, resolved = .prepareError error)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    others = [] ∧ next = connection := by
  obtain ⟨resolved', after', value, same, -, -, -, -, -, nextEq, -⟩ := runScriptStep_continued_spec step
  rw [found] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
  have single : resolved.fromQuery = false := by
    rcases readOnly with ⟨query, subqueries, rfl⟩ | ⟨error, rfl⟩ <;> rfl
  have ordinary : resolved.isControl = false := by
    rcases readOnly with ⟨query, subqueries, rfl⟩ | ⟨error, rfl⟩ <;> rfl
  have afterEq := resolveStatement_after context _ _ _ _ found
  rw [ResolveState.after_of_isControl _ ordinary] at afterEq
  obtain ⟨okFrame, errorFrame⟩ := runStatement_readOnly_effect readOnly value
    (connection.state.counters.view resolved.counterReads) parameters connection.state.database
  have noCounts : (connection.state.statementRun value parameters resolved).counts = {} := by
    rcases readOnly with ⟨query, subqueries, rfl⟩ | ⟨error, rfl⟩ <;> rfl
  have foreignKeys : after.foreignKeys = connection.foreignKeys := by rw [afterEq]; rfl
  have recursiveTriggers : after.recursiveTriggers = connection.recursiveTriggers := by rw [afterEq]; rfl
  rw [nextEq, advanceRun_ordinary index resolved connection.state _ ordinary]
  obtain ⟨database, same, equal⟩ := afterStep_frame connection after index (connection.state.statementRun value parameters resolved)
    (fun database => database = connection.state.database) rfl foreignKeys recursiveTriggers okFrame errorFrame
  rw [equal, noCounts, same, Counters.apply_default]
  exact ⟨runScriptStep_others step found single, rfl⟩

end Belay.Sqlite.Model
