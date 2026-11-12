import Belay.Sqlite.Model.Schema.Columns.AddColumn
import Belay.Sqlite.Model.Schema.Writes.InsertCells
import Belay.Sqlite.Model.Queries.Preparation.Writes
import Belay.Sqlite.Model.Schema.Triggers.ScopeNames
import Belay.Sqlite.Model.Schema.Writes.ConflictPolicy

set_option doc.verso true

/-! Name resolution of INSERT and UPDATE. The checks follow the order of SQLite
3.51.0's {lit}`sqlite3MultiValues`, {lit}`sqlite3Insert` and {lit}`sqlite3Update`.
A resolved INSERT row has one value for each table column in table order: a named
column gets the written value and every other column its default. -/

namespace Belay.Sqlite.Model

/-- Resolve INSERT. Path 1 is the column list, path 2 the rows, path 3 the
{lit}`ON CONFLICT` clauses ({name}`resolveConflictTraced`) and path 5 the {lit}`RETURNING`
columns. An INSERT without clauses whose algorithms are all ABORT
({name}`insertPolicy`) is {name}`Resolved.Statement.insert`; any other INSERT is
{name}`Resolved.Statement.upsert`. The values may name the statement's resolved subqueries,
whose shapes are {lit}`shapes`. A view target is {name}`resolveViewModify`, after the check of the rows.
The trace holds the table at path 0, the names of the column list, the names of the values, of the
clauses and of the {lit}`RETURNING` columns, in the order in which the resolver reaches them. -/
def resolveInsertTraced (context : ResolveContext) (catalog : Catalog) (tableName : Identifier)
    (names : Option (List Identifier)) (rows : List (List Syntax.Expr)) (conflicts : List Syntax.ConflictClause)
    (algorithm : Option ConflictAlgorithm) (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query)
    (shapes : SubqueryShapes) (trigger : Option TriggerRow := none) : TracedResolution :=
  let dqs := context.profile.dqsDml
  let width := (rows.head?.map List.length).getD 0
  if rows.any (·.length != width) then Traced.lift (prepareError catalog (.expression .valuesDiffer)) else
  Traced.withTarget catalog tableName false (Traced.lift (resolveViewModify catalog tableName))
    (Traced.lift (prepareError catalog (.noSuchTable tableName))) fun position table =>
  let scope := Scope.singleAt (some position) tableName table.columns !table.withoutRowid
  if insertRowidTarget table names then Traced.lift (restrict [1] .rowidName) else
  Traced.stage catalog [1] ((insertPositionsTraced tableName table.columns scope names).mapError ValueIssue.prepare)
    fun positions =>
  let around := (trigger.map (·.scope 0)).getD []
  Traced.stage catalog [2] (resolveAllTraced (fun row values =>
      ((resolveAllTraced (fun column item => (constantCellTraced dqs shapes item around).underTrace [column])
        values).mapError (·.under [row])).underTrace [row]) rows) fun values =>
  if names.isNone && width != positions.length then
    Traced.lift (prepareError catalog (.expression (.valueCount tableName positions.length width)))
  else if names.isSome && width != positions.length then
    Traced.lift (prepareError catalog (.expression (.valuesForColumns width positions.length)))
  else if positions.eraseDups.length != positions.length then
    Traced.lift (restrict [1] .insertColumnTwice)
  else Traced.stage catalog [2] (Traced.lift (resolveAll (fun _ row => fullCells table.columns positions row) values))
    fun full =>
  let keys := catalog.uniqueKeys position table
  Traced.stage catalog [3] (resolveAllTraced (resolveConflictTraced dqs tableName position table keys) conflicts)
    fun clauses =>
  Traced.stage catalog [insertReturningField] (resolveReturningTraced dqs scope returning) fun columns =>
  let policy := catalog.writePolicy position table algorithm
  if policy.mixed then Traced.lift (restrict [] .mixedConflictAlgorithms)
  else if replacesDefault table policy then Traced.lift (restrict [] .replaceDefault)
  else if clauses.isEmpty && policy.aborts then Traced.ok (.insert position full columns subqueries, catalog)
  else Traced.ok (.upsert position full clauses columns algorithm subqueries, catalog)

/-- The resolution of an INSERT: {name}`resolveInsertTraced` without its trace. -/
def resolveInsert (context : ResolveContext) (catalog : Catalog) (tableName : Identifier)
    (names : Option (List Identifier)) (rows : List (List Syntax.Expr)) (conflicts : List Syntax.ConflictClause)
    (algorithm : Option ConflictAlgorithm) (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query)
    (shapes : SubqueryShapes) (trigger : Option TriggerRow := none) : StatementResolution :=
  (resolveInsertTraced context catalog tableName names rows conflicts algorithm returning subqueries shapes trigger).drop

end Belay.Sqlite.Model
