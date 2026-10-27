import Belay.Sqlite.Model.SuccessfulScriptEffects
import Belay.Sqlite.Model.FailedStepFrame

set_option doc.verso true

/-! The step of a statement that fails only as {lit}`ExecutionError.unmodeled` (ADR 0017, S6). Such a
statement either ends the run, because the model does not describe it on the database, or continues
with an effect that succeeds. A step of it therefore has no error output, and the next connection is
fixed by the database that the effect gives. CREATE TABLE, the plain DROP TABLE, the rename of a
table and the setting pragmas are statements of this kind. -/

namespace Belay.Sqlite.Model

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

end Belay.Sqlite.Model
