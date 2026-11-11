import Belay.Sqlite.Model.Queries.Evaluation.SourceScanOrders
import Belay.Sqlite.Model.Queries.Evaluation.QueryRun
import Belay.Sqlite.Model.Queries.Evaluation.PossibleResults
import Belay.Sqlite.Model.Queries.Evaluation.QueryFunctions

set_option doc.verso true

namespace Belay.Sqlite.Model

namespace Resolved

/-- Whether the query reads one table by a scan, row by row, without a step that holds rows back: one
table as the only source, no compound, no aggregate, no {lit}`DISTINCT`, no {lit}`ORDER BY`, and no
{lit}`OFFSET` (after the binding of a parameter of the window, {name}`Query.bindWindow`). SQLite then evaluates the {lit}`WHERE` condition and the result columns of each row
when it reads the row, so the first row that fails stops the production. -/
def Query.scansRows (query : Query) : Bool :=
  query.compound.isNone && !query.aggregate && query.groupBy.isEmpty && query.distinct.isNone &&
    query.orderBy.isEmpty && query.offset == 0 &&
    (match query.sources with
      | [join] => (match join.source with
        | .table _ => true
        | .initialTable _ | .each .. | .subquery .. | .pragma _ => false)
      | [] | _ :: _ :: _ => false)

/-- The fault of reading one source row of a query that {name}`Query.scansRows`: the fault of the
{lit}`WHERE` condition, else, for a row that it keeps, the fault of the result columns. -/
def Query.rowFault (context : EvalContext) (query : Query) (row : List Value) : Fault :=
  let columns := (query.columns.flatMap Output.scalars).foldl (fun fault term => fault.join (term.evaluate context row).2) Fault.none
  match query.filter with
  | none => columns
  | some condition =>
    let (value, fault) := condition.evaluate context row
    if fault != .none then fault else if truthy value then columns else .none

/-- Whether the query gives its rows in an order that the model describes without a choice of
SQLite: a total {lit}`ORDER BY`, where the rows of each group of equal sort keys are the same row. -/
def Query.totallyOrdered (context : EvalContext) (query : Query) (rows : List (List Value)) : Bool :=
  !query.orderBy.isEmpty && (query.tieGroupRows context rows).all fun group => group.eraseDups.length ≤ 1

/-- Whether a {lit}`WHERE` condition has an {lit}`OR`, which SQLite may answer with several indexes
one after the other. -/
def Query.hasOrCondition (query : Query) : Bool :=
  query.filter.any (·.any fun term => term matches .or ..)

end Resolved

end Belay.Sqlite.Model
