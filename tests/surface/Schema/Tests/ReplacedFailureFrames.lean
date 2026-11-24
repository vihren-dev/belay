import Belay

set_option doc.verso true

/-! Original group contracts under ADR 0033, checked through the last change to their dependencies. -/

namespace Belay.Sqlite.ReplacedFrames
open Belay.Sqlite.Model

/-- For every connection, ordinary statement that is not a query, and step that continues with an error
output: if each error of the run of the statement has a reason other than
{name}`ExecutionError.constraintFail` and {name}`ExecutionError.constraintRollback`, then the next connection
is the connection with the counters of the run, for some clock value. In plain words, a failed statement
changes nothing but the counters. Proof sketch: an effect that succeeds publishes a transition that does not
halt, so the output is no error ({name}`Output.ofStep_isError_of_noHalt`); so the effect fails, and
{name}`afterStep_frame` reads the connection after a failure. -/
theorem runScriptStep_failed_frame {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {resolved : Resolved.Statement} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (ordinary : resolved.isControl = false)
    (notQuery : ∀ query subqueries, resolved ≠ .query query subqueries)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (failed : output.isError = true)
    (errorFrame : ∀ value reason reached,
      (connection.state.statementRun value parameters resolved).effect = .error (reason, reached) →
        reason ≠ .constraintFail ∧ reason ≠ .constraintRollback) :
    ∃ value, next = { connection with state := { connection.state with
        counters := connection.state.counters.apply (connection.state.statementRun value parameters resolved).counts } } := by
  obtain ⟨resolved', after', value, same, -, -, -, ofStep, -, nextEq, -⟩ := runScriptStep_continued_spec step
  rw [found] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
  have afterEq := (resolveStatement_certificate context _ _ _ _ found).after
  rw [ResolveState.after_of_isControl _ ordinary] at afterEq
  rw [nextEq, advanceRun_ordinary index resolved connection.state _ ordinary]
  have foreignKeys : after.foreignKeys = connection.foreignKeys := by rw [afterEq]; rfl
  have recursiveTriggers : after.recursiveTriggers = connection.recursiveTriggers := by rw [afterEq]; rfl
  refine ⟨value, ?_⟩
  cases effect : (connection.state.statementRun value parameters resolved).effect with
  | ok database =>
    exfalso
    rw [← ofStep, advanceRun_ordinary index resolved connection.state _ ordinary, effect] at failed
    rw [Output.ofStep_isError_of_noHalt _ _ _ _ _ _ _ notQuery (by
      simp [SqlTransition.counted, SqlState.publish, haltError])] at failed
    cases failed
  | error failure =>
    obtain ⟨reason, reached⟩ := failure
    obtain ⟨notFail, notRollback⟩ := errorFrame value reason reached effect
    rcases snapshot : connection.state.snapshot with _ | original <;>
      simp [SqlState.publish, SqlTransition.counted, Connection.afterStep, Connection.afterError,
        SqlState.failed, SqlState.finish, notFail, notRollback, snapshot, foreignKeys, recursiveTriggers]

/-- For every connection, statement that resolves to a plain write, and step that continues with an error
output: the next connection is the connection with the counters of the run, for some clock value. In plain
words, a failed plain write changes nothing but the counters. Proof sketch:
{name}`runScriptStep_failed_frame` with the error reasons of {name}`runStatement_plainWrite_effect`. -/
theorem runScriptStep_plainWrite_failed {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {resolved : Resolved.Statement} {after : ResolveState} {target : Nat}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (plain : resolved.plainWriteTarget = some target)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (failed : output.isError = true) :
    ∃ value, next = { connection with state := { connection.state with
        counters := connection.state.counters.apply (connection.state.statementRun value parameters resolved).counts } } := by
  have notQuery : ∀ query subqueries, resolved ≠ .query query subqueries := by
    intro query subqueries same; subst same; simp [Resolved.Statement.plainWriteTarget] at plain
  have ordinary : resolved.isControl = false := by
    cases resolved <;> simp_all [Resolved.Statement.plainWriteTarget, Resolved.Statement.isControl]
  refine runScriptStep_failed_frame found ordinary notQuery step failed fun value reason reached effect => ?_
  exact (runStatement_plainWrite_effect plain value
    (connection.state.counters.view resolved.counterReads) parameters connection.state.database).2 reason reached effect

#print axioms runScriptStep_failed_frame
#print axioms runScriptStep_plainWrite_failed

end Belay.Sqlite.ReplacedFrames
