import Belay.Sqlite.Resolution.Definitions
import Belay.Sqlite.Resolution.Upserts
import Belay.Sqlite.Resolution.InsertCells

set_option doc.verso true

/-! Name resolution of INSERT and UPDATE. The checks follow the order of SQLite
3.51.0's {lit}`sqlite3MultiValues`, {lit}`sqlite3Insert` and {lit}`sqlite3Update`.
A resolved INSERT row has one value for each table column in table order: a named
column gets the written value and every other column its default. -/

namespace Belay.Sqlite

/-- Turn a value issue into the statement's resolution: a prepare error keeps the
catalog, a restriction refuses the script. -/
def issueResolution (catalog : Catalog) (index : Nat) (path : List Nat) : ValueIssue → StatementResolution
  | .prepare error => prepareError catalog (.expression error)
  | .restriction inner reason => restrict index (path ++ inner) reason

/-- The table column positions of an INSERT column list, or
{lit}`table %S has no column named %s` for the first unknown name. -/
def insertPositions (tableName : Identifier) (columns : List CatalogColumn) :
    List Identifier → Except ExprError (List Nat)
  | [] => .ok []
  | name :: rest => match columnPosition columns name with
    | some position => (insertPositions tableName columns rest).map (position :: ·)
    | none => .error (.tableHasNoColumn tableName name)

/-- Resolve INSERT. Path 1 is the column list, path 2 the rows, path 3 the
{lit}`ON CONFLICT` clauses ({name}`resolveConflict`) and path 5 the {lit}`RETURNING`
columns. An INSERT without clauses whose algorithms are all ABORT
({name}`insertPolicy`) is {name}`Resolved.Statement.insert`; any other INSERT is
{name}`Resolved.Statement.upsert`. -/
def resolveInsert (context : ResolveContext) (catalog : Catalog) (index : Nat) (tableName : Identifier)
    (names : Option (List Identifier)) (rows : List (List Syntax.Expr)) (conflicts : List Syntax.ConflictClause)
    (algorithm : Option ConflictAlgorithm) (returning : List Syntax.ResultColumn) : StatementResolution :=
  let width := (rows.head?.map List.length).getD 0
  if rows.any (·.length != width) then prepareError catalog (.expression .valuesDiffer) else
  match catalog.findTable tableName with
  | none => prepareError catalog (.noSuchTable tableName)
  | some (position, table) =>
    let positions := match names with
      | some written => insertPositions tableName table.columns written
      | none => .ok (List.range table.columns.length)
    match positions with
    | .error error => prepareError catalog (.expression error)
    | .ok positions =>
      match resolveAll (fun row values => (resolveAll (fun _ => constantCell context.profile.dqsDml)
          values).mapError (·.under [row])) rows with
      | .error issue => issueResolution catalog index [2] issue
      | .ok values =>
        if names.isNone && width != table.columns.length then
          prepareError catalog (.expression (.valueCount tableName table.columns.length width))
        else if names.isSome && width != positions.length then
          prepareError catalog (.expression (.valuesForColumns width positions.length))
        else if positions.eraseDups.length != positions.length then
          restrict index [1] .insertColumnTwice
        else match resolveAll (fun _ row => fullCells table.columns positions row) values with
          | .error issue => issueResolution catalog index [2] issue
          | .ok full =>
            let keys := catalog.uniqueKeys position table
            match resolveAll (resolveConflict context.profile.dqsDml tableName table keys) conflicts with
            | .error issue => issueResolution catalog index [3] issue
            | .ok clauses =>
              match resolveReturning context.profile.dqsDml (Scope.single tableName table.columns) returning with
              | .error issue => issueResolution catalog index [insertReturningField] issue
              | .ok columns =>
                let policy := catalog.writePolicy position table algorithm
                if policy.mixed then restrict index [] .mixedConflictAlgorithms
                else if replacesDefault table policy then restrict index [] .replaceDefault
                else if clauses.isEmpty && policy.aborts then
                  .ok (.insert position full columns, catalog)
                else .ok (.upsert position full clauses columns algorithm, catalog)

end Belay.Sqlite
