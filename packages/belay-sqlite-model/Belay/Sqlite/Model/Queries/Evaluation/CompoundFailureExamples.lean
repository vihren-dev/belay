import Belay.Sqlite.Model.Queries.Evaluation.CompoundExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved.CompoundExamples

/-- The term that fails. -/
def failingTerm : Query := literals [failing]

/-- The value {lit}`'x'` for {lit}`LIMIT ?`, which is not an integer. -/
def notInteger : List Value := [.text [120]]

/-- {lit}`SELECT (compound)` with the compound as subquery 0 and its terms after it. -/
def scalarStatement : Query := { literals [.subquery 0] with names := ["s"] }

/-- A compound subquery at index 0 over the terms at indexes 1 to n. -/
def subqueryCompound (operators : List CompoundOperator) : Query :=
  let rest := operators.zipIdx.map fun (operator, index) => (operator, index + 2)
  let terms : Compound := { first := 1, rest, collations := [.binary] }
  { compound operators [.binary] with compound := some terms }

end Belay.Sqlite.Model.Resolved.CompoundExamples
