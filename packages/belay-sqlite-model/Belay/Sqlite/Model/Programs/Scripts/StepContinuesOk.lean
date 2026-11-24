import Belay.Sqlite.Model.Programs.Scripts.OrdinaryStepEffects
import Belay.Sqlite.Model.Programs.Scripts.StepContinues
import Belay.Sqlite.Model.Programs.Scripts.ResolvedStepGuards

set_option doc.verso true

/-! A successful plain DROP or catalog rewrite continues once without an error. The shared output law reads success from the transition. -/

namespace Belay.Sqlite.Model

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

end Belay.Sqlite.Model
