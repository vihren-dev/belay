import Belay.Sqlite.Model.SuccessfulScriptEffects

set_option doc.verso true

/-!
The output of a step of a statement that is not a query (ADR 0017, S6). Only a query step can permit
several results ({lit}`Output.oneOf`): every other statement gives a count of changes, rows of a
RETURNING clause, an error or a stop. A rule about the executions of a program of such statements
then has one observation for each step.
-/

namespace Belay.Sqlite.Model

/-- For every clock, parameters, statement that is not a query, state, run and transition: the output of
the step is never a choice between results. Proof sketch: unfold the output; a halt gives an error or a
stop, and the other cases give rows, a count or a stop. -/
theorem Output.ofStep_ne_oneOf_of_not_query (clock : Int) (parameters : List Value) (statement : Resolved.Statement)
    (before : SqlState) (run : StatementRun) (transition : SqlTransition)
    (notQuery : ∀ query subqueries, statement ≠ .query query subqueries)
    (alternatives : List (List (List Value))) :
    Output.ofStep clock parameters statement before run transition ≠ .oneOf alternatives := by
  unfold Output.ofStep
  rcases haltError transition with _ | failure
  · dsimp only
    cases statement with
    | query query subqueries => exact absurd rfl (notQuery query subqueries)
    | _ =>
      dsimp only
      split
      · split <;> simp
      · simp
  · cases failure <;> simp

/-- For every connection, statement that resolves to a statement that is not a query, and step that
continues: the output of the step is not a choice between results. Proof sketch:
{name}`runScriptStep_ran` gives the output as {name}`Output.ofStep` of the resolved statement, which
{name}`Output.ofStep_ne_oneOf_of_not_query` treats. -/
theorem runScriptStep_ne_oneOf_of_not_query {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {resolved : Resolved.Statement} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (notQuery : ∀ query subqueries, resolved ≠ .query query subqueries)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (alternatives : List (List (List Value))) : output ≠ .oneOf alternatives := by
  obtain ⟨resolved', later, value, same, -, -, -, outputEq, -⟩ := runScriptStep_ran step
  rw [found] at same
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj same)
  rw [outputEq]
  exact Output.ofStep_ne_oneOf_of_not_query _ _ _ _ _ _ notQuery alternatives

end Belay.Sqlite.Model
