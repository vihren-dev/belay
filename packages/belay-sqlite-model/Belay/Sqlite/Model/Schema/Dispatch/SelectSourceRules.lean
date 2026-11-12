import Belay.Sqlite.Model.Queries.Evaluation.StatementQuiet
import Belay.Sqlite.Model.Schema.Dispatch.PlainQueryRules
import Belay.Sqlite.Model.Schema.Dispatch.TableInfoResolution

set_option doc.verso true

/-! The source rules of a query without a table (ADR 0027, A20): the rows of a pragma, and the rows
of a {lit}`json_each` call, as the only source of the query. A query without {lit}`FROM` has the one
row with no cells ({lit}`Query.source_none`). A {lit}`json_each` call that fails keeps its fault:
the source has the fault {lit}`Fault.may`, and the model describes no result of the statement. A
statement without {lit}`FROM` whose expressions are quiet is quiet ({lit}`Statement.Quiet.selectNoFrom`). -/

namespace Belay.Sqlite.Model.Resolved

/-- Pragma source rule: for every context, database, optional initial database, query, pragma rows
{lit}`pragma` and rows {lit}`rows`, when the only source of the query is {lit}`pragma` as an inner
join without a condition and the model gives the rows {lit}`rows` of {lit}`pragma` over the database
({name}`PragmaRows.rowsOn`), the source rows of the query are {lit}`rows`, with the width field of
the pragma ({name}`PragmaRows.width`) and no fault. The rule does not prove that each row has that
number of cells. For example, the rows of {lit}`PRAGMA table_info(t)` are fixed rows that
resolution computes from the catalog. Proof sketch: the join of an inner source without a condition
keeps the concatenation of the one empty row with each row of the pragma. -/
theorem Query.source_pragma (context : EvalContext) (database : Database) (initial : Option Database) (query : Query)
    (pragma : PragmaRows) (rows : List (List Value))
    (single : query.sources = [{ kind := .inner, source := .pragma pragma, condition := none }])
    (given : pragma.rowsOn database = some rows) :
    query.source context database initial = some { rows, width := pragma.width, fault := .none } := by
  simp [Query.source, single, List.foldlM, QuerySource.join, given, joinRows, joinRow, joinMatches,
    QuerySource.matches, bind, Option.bind, pure]

/-- {lit}`json_each` source rule: for every context, database, optional initial database, query,
JSON expression {lit}`json`, optional path expression {lit}`path` and rows {lit}`rows`, when the only
source of the query is {lit}`json_each(json, path)` as an inner join without a condition and
{name}`Json.eachRows` of the values of the arguments over the empty row gives {lit}`rows`, the source
rows of the query are {lit}`rows`, with the width field {name}`eachWidth` and no fault. Proof
sketch: the one empty row is the only row so far; the join without a condition keeps each JSON row
after it, and no call fails. -/
theorem Query.source_each (context : EvalContext) (database : Database) (initial : Option Database) (query : Query)
    (json : Expr) (path : Option Expr) (rows : List (List Value))
    (single : query.sources = [{ kind := .inner, source := .each json path, condition := none }])
    (parsed : Json.eachRows (json.eval context []) (path.map (·.eval context [])) = .ok rows) :
    query.source context database initial = some { rows, width := eachWidth, fault := .none } := by
  simp [Query.source, single, List.foldlM, QuerySource.join, parsed, joinRow, joinMatches,
    QuerySource.matches, bind, Option.bind, pure, Except.toOption]

/-- {lit}`json_each` fault rule: for every context, database, optional initial database, query,
JSON expression {lit}`json`, optional path expression {lit}`path` and JSON error, when the only
source of the query is {lit}`json_each(json, path)` as an inner join without a condition and
{name}`Json.eachRows` of the values of the arguments over the empty row gives the error, the source
rows of the query are no rows, with the width field {name}`eachWidth` and the fault {name}`Fault.may`. The fault is not removed: the model
describes no result of a statement over these source rows, also not the empty result. Proof
sketch: the call over the one empty row fails, so it gives no row and the fold joins the fault
{name}`Fault.may` to the fault {name}`Fault.none` of the start. -/
theorem Query.source_each_fault (context : EvalContext) (database : Database) (initial : Option Database)
    (query : Query) (json : Expr) (path : Option Expr) (error : Json.JsonError)
    (single : query.sources = [{ kind := .inner, source := .each json path, condition := none }])
    (failed : Json.eachRows (json.eval context []) (path.map (·.eval context [])) = .error error) :
    query.source context database initial = some { rows := [], width := eachWidth, fault := .may } := by
  simp [Query.source, single, List.foldlM, QuerySource.join, failed, joinRow, joinMatches,
    QuerySource.matches, bind, Option.bind, pure, Except.toOption]
  rfl

end Belay.Sqlite.Model.Resolved
