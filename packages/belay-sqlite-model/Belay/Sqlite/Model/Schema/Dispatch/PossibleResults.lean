import Belay.Sqlite.Model.Schema.Dispatch.Execution
import Belay.Sqlite.Model.Queries.Evaluation.PossibleResults

set_option doc.verso true

/-! The results that SQLite may give for a query (ADR 0018, D6). SQLite promises the order of
{lit}`ORDER BY` only: rows that its terms do not separate, and every row of a query without
{lit}`ORDER BY`, may come in any order. So the model gives each result in a normal form, the rows of
each tie group sorted by {lit}`compareNormal`, and gives every result
that a window cuts out of the groups: a group that {lit}`LIMIT` or {lit}`OFFSET` cuts may give any of its
rows that the window takes. {lit}`PossibleResultsLaws.lean` relates the list to the one result
of {lit}`Query.results`. -/

namespace Belay.Sqlite.Model

/-- Every result that SQLite may give for a statement's query over a database at a clock value
with the counters and the values bound to the statement's parameters ({name}`Resolved.Query.possibleResults`),
in the context of its subqueries, as
{name}`Resolved.Query.runOn` gives its one result, with its window bound to the values
({name}`Resolved.Query.bindWindow`); none when a table is missing or a value of the window is not
an integer. The optional {lit}`initial` database is the one that the sources of the initial origin read; use
none outside a two-state observation. -/
def Resolved.Query.possibleOn (query : Resolved.Query) (clock : Int) (counters : Counters) (parameters : List Value) (database : Database)
    (subqueries : List Resolved.Query) (initial : Option Database := none) : Option (List (List (List Value))) :=
  let context := Resolved.statementContext clock counters parameters database subqueries initial
  (query.source context database initial).bind fun source =>
    (query.bindWindow parameters).map fun bound => bound.possibleResults context source.rows

end Belay.Sqlite.Model
