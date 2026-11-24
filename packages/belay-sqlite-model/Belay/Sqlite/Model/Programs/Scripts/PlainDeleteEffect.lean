import Belay.Sqlite.Model.Programs.Scripts.SuccessfulScriptEffects
import Belay.Sqlite.Model.Programs.Scripts.KeysUniqueWrites
import Belay.Sqlite.Model.Schema.Writes.PlainInsertEffect
import Belay.Sqlite.Model.Programs.Scripts.StepRuleProjections

set_option doc.verso true

/-! The no-choice laws of DELETE cover every RETURNING list and write-rule mode.
The exact step without RETURNING or write rules is given in {lit}`PlainDeleteRule.lean`. -/

namespace Belay.Sqlite.Model

/-- For every clock, statement values, state, run, transition, target and rule fields: the output of a step
of a delete is never a choice between results. Proof sketch: unfold the output and split on the halt reason;
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
