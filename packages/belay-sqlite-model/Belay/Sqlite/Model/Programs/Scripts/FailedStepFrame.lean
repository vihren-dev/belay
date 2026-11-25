import Belay.Sqlite.Model.Programs.Scripts.PlainWriteFrame

set_option doc.verso true

/-! The output of an ordinary statement without a halt cannot report an error. -/

namespace Belay.Sqlite.Model

/-- For every clock, parameters, statement that is not a query, state, run, transition and initial
database: if the transition does not halt, the output of the step is not an error. Proof sketch: unfold the
output; without a halt it is the output of a query, which the premise excludes, or rows, a count of changes
or a stop of the model, and none of them is an error. -/
theorem Output.ofStep_isError_of_noHalt (clock : Int) (parameters : List Value) (statement : Resolved.Statement)
    (before : SqlState) (run : StatementRun) (transition : SqlTransition) (initial : Option Database)
    (notQuery : ∀ query subqueries, statement ≠ .query query subqueries) (calm : haltError transition = none) :
    (Output.ofStep clock parameters statement before run transition initial).isError = false := by
  unfold Output.ofStep
  simp only [calm]
  split
  all_goals first
    | (exfalso; exact notQuery _ _ rfl)
    | (exfalso; exact notQuery _ _ (by assumption))
    | (split <;> (try split) <;> rfl)

end Belay.Sqlite.Model
