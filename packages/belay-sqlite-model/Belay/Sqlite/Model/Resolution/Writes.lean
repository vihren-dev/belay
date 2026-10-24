import Belay.Sqlite.Model.Resolution.AddColumn
import Belay.Sqlite.Model.Resolution.Upserts
import Belay.Sqlite.Model.Resolution.InsertCells

set_option doc.verso true

/-! Name resolution of INSERT and UPDATE. The checks follow the order of SQLite
3.51.0's {lit}`sqlite3MultiValues`, {lit}`sqlite3Insert` and {lit}`sqlite3Update`.
A resolved INSERT row has one value for each table column in table order: a named
column gets the written value and every other column its default. -/

namespace Belay.Sqlite.Model

/-- The table column positions of an INSERT column list, or
{lit}`table %S has no column named %s` for the first unknown name, or
{lit}`cannot INSERT into generated column "%s"` for a generated column. -/
def insertPositions (tableName : Identifier) (columns : List CatalogColumn) :
    List Identifier → Except ExprError (List Nat)
  | [] => .ok []
  | name :: rest => match columnPosition columns name with
    | some position =>
      if (columns[position]?.bind (·.generated)).isSome then .error (.insertGenerated name)
      else (insertPositions tableName columns rest).map (position :: ·)
    | none => .error (.tableHasNoColumn tableName name)

/-- The positions that an INSERT without a column list fills: every column that is not
generated, in table order (ADR 0014, slice 5). -/
def writablePositions (columns : List CatalogColumn) : List Nat :=
  (List.range columns.length).filter fun position => (columns[position]?.bind (·.generated)).isNone

/-- Resolve INSERT. Path 1 is the column list, path 2 the rows, path 3 the
{lit}`ON CONFLICT` clauses ({name}`resolveConflict`) and path 5 the {lit}`RETURNING`
columns. An INSERT without clauses whose algorithms are all ABORT
({name}`insertPolicy`) is {name}`Resolved.Statement.insert`; any other INSERT is
{name}`Resolved.Statement.upsert`. The values may name the statement's resolved subqueries,
whose shapes are {lit}`shapes`. An unexpanded view target is a model restriction. -/
def resolveInsert (context : ResolveContext) (catalog : Catalog) (tableName : Identifier)
    (names : Option (List Identifier)) (rows : List (List Syntax.Expr)) (conflicts : List Syntax.ConflictClause)
    (algorithm : Option ConflictAlgorithm) (returning : List Syntax.ResultColumn) (subqueries : List Resolved.Query)
    (shapes : SubqueryShapes) (trigger : Option TriggerRow := none) : StatementResolution :=
  let width := (rows.head?.map List.length).getD 0
  if rows.any (·.length != width) then prepareError catalog (.expression .valuesDiffer) else
  match catalog.findTable tableName with
  | none => if (catalog.findView tableName).isSome then restrict [0] .subqueryHere
      else prepareError catalog (.noSuchTable tableName)
  | some (position, table) =>
    let positions := match names with
      | some written => insertPositions tableName table.columns written
      | none => .ok (writablePositions table.columns)
    match positions with
    | .error error => prepareError catalog (.expression error)
    | .ok positions =>
      let around := (trigger.map (·.scope 0)).getD []
      match resolveAll (fun row values => (resolveAll (fun _ item => constantCell context.profile.dqsDml shapes item around)
          values).mapError (·.under [row])) rows with
      | .error issue => issueResolution catalog [2] issue
      | .ok values =>
        if names.isNone && width != positions.length then
          prepareError catalog (.expression (.valueCount tableName positions.length width))
        else if names.isSome && width != positions.length then
          prepareError catalog (.expression (.valuesForColumns width positions.length))
        else if positions.eraseDups.length != positions.length then
          restrict [1] .insertColumnTwice
        else match resolveAll (fun _ row => fullCells table.columns positions row) values with
          | .error issue => issueResolution catalog [2] issue
          | .ok full =>
            let keys := catalog.uniqueKeys position table
            match resolveAll (resolveConflict context.profile.dqsDml tableName table keys) conflicts with
            | .error issue => issueResolution catalog [3] issue
            | .ok clauses =>
              match resolveReturning context.profile.dqsDml (Scope.single tableName table.columns !table.withoutRowid) returning with
              | .error issue => issueResolution catalog [insertReturningField] issue
              | .ok columns =>
                let policy := catalog.writePolicy position table algorithm
                if policy.mixed then restrict [] .mixedConflictAlgorithms
                else if replacesDefault table policy then restrict [] .replaceDefault
                else if clauses.isEmpty && policy.aborts then
                  .ok (.insert position full columns subqueries, catalog)
                else .ok (.upsert position full clauses columns algorithm subqueries, catalog)

end Belay.Sqlite.Model
