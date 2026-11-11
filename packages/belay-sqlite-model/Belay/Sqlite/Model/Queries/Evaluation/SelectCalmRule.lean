import Belay.Sqlite.Model.Queries.Evaluation.SelectRunRule
import Belay.Sqlite.Model.Queries.Evaluation.StatementQuiet
import Belay.Sqlite.Model.Queries.Evaluation.QueryPlainLaws
import Belay.Sqlite.Model.Queries.Evaluation.QueryStatementOutput

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The context in which a calm statement without subqueries evaluates its expressions: the clock
value 0, no counter, and the values bound to its parameters. -/
abbrev Resolved.EvalContext.bound (parameters : List Value) : Resolved.EvalContext :=
  { Resolved.EvalContext.plain 0 with parameters }

/-- For every list of values, the values bound to the parameters of the context of the values are the values. Proof
sketch: the definition computes. -/
theorem Resolved.EvalContext.bound_parameters (parameters : List Value) :
    (Resolved.EvalContext.bound parameters).parameters = parameters := rfl

end Belay.Sqlite.Model
