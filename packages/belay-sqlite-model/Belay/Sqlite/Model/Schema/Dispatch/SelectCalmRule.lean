import Belay.Sqlite.Model.Schema.Dispatch.SelectRunRule
import Belay.Sqlite.Model.Queries.Evaluation.SelectCalmRule

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The context in which a calm query statement evaluates its query and its subqueries: the
clock value 0, no counter, the values bound to its parameters, and the runs of its subqueries over
the database ({name}`Resolved.statementContext`). Without subqueries it is the context of the values
({name}`Resolved.EvalContext.bound`). -/
abbrev Resolved.EvalContext.statement (parameters : List Value) (database : Database)
    (subqueries : List Resolved.Query) : Resolved.EvalContext :=
  Resolved.statementContext 0 {} parameters database subqueries

end Belay.Sqlite.Model
