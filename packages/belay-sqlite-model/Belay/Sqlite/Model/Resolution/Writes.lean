import Belay.Sqlite.Model.Resolution.AddColumn
import Belay.Sqlite.Model.Resolution.Upserts
import Belay.Sqlite.Model.Resolution.InsertCells
import Belay.Sqlite.Model.Resolution.WriteStages

set_option doc.verso true

/-! Name resolution of INSERT and UPDATE. The checks follow the order of SQLite
3.51.0's {lit}`sqlite3MultiValues`, {lit}`sqlite3Insert` and {lit}`sqlite3Update`.
A resolved INSERT row has one value for each table column in table order: a named
column gets the written value and every other column its default. -/

namespace Belay.Sqlite.Model

/-- The name of a view as the catalog spells it, or the name as written when there is none. -/
def viewCatalogName (catalog : Catalog) (view : Identifier) : Identifier :=
  (((catalog.findView view).bind fun (position, _) => catalog[position]?.map (·.name))).getD view

/-- The resolution of a write (INSERT, UPDATE or DELETE) whose target is a view: SQLite refuses it
with {lit}`cannot modify %s because it is a view`, because the model holds no INSTEAD OF trigger.
The name keeps the catalog's spelling. Before that, SQLite reads the columns of the view
({lit}`resolveViewTarget`). -/
def resolveViewModify (catalog : Catalog) (view : Identifier) : StatementResolution :=
  prepareError catalog (.viewModify (viewCatalogName catalog view))

/-- The table column positions of an INSERT column list from the name at {lit}`index`, or
{lit}`table %S has no column named %s` for the first unknown name, or
{lit}`cannot INSERT into generated column "%s"` for a generated column. Each name is recorded at
{lit}`[index]`, as the column of the table that it names, with the columns of the table as candidates
when it names none; {lit}`scope` is the scope of the table. -/
def insertPositionsFrom (tableName : Identifier) (columns : List CatalogColumn) (scope : Scope) :
    Nat → List Identifier → Traced ExprError (List Nat)
  | _, [] => pure []
  | index, name :: rest => do
    let located := columnPosition columns name
    Traced.record (columnTargetOccurrence scope [index] name located .error)
    match located with
    | some position =>
      if (columns[position]?.bind (·.generated)).isSome then throw (.insertGenerated name)
      else do
        let positions ← insertPositionsFrom tableName columns scope (index + 1) rest
        pure (position :: positions)
    | none => throw (.tableHasNoColumn tableName name)

/-- The positions that an INSERT without a column list fills: every column that is not
generated, in table order (ADR 0014, slice 5). -/
def writablePositions (columns : List CatalogColumn) : List Nat :=
  (List.range columns.length).filter fun position => (columns[position]?.bind (·.generated)).isNone

/-- The positions of the cells that an INSERT fills: those of its column list, or without a list every
column that is not generated ({name}`writablePositions`). The column list is at child 1. -/
def insertPositionsTraced (tableName : Identifier) (columns : List CatalogColumn) (scope : Scope) :
    Option (List Identifier) → Traced ExprError (List Nat)
  | some written => insertPositionsFrom tableName columns scope 0 written
  | none => pure (writablePositions columns)

/-- The resolved {lit}`WHERE` filter of an UPDATE or DELETE, a condition over {lit}`scope`, or none
when there is no filter. -/
def resolveWriteFilterTraced (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) :
    Option Syntax.Expr → Traced ValueIssue (Option Resolved.Expr)
  | none => pure none
  | some term => Traced.map some (Traced.condition [] (resolveOperandTraced dqs scope shapes true term))

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
