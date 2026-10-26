import Belay.Sqlite.Model.Resolution.Writes
import Belay.Sqlite.Model.Resolution.WriteResolution
import Belay.Sqlite.Model.Resolution.SelectResolution

set_option doc.verso true

/-! Preparation of INSERT from a query (ADR 0017, S6; ADR 0019, D4). The checks follow the order
of SQLite 3.51.0's {lit}`sqlite3Insert`, which the native probes of the task file confirm: the table
(a view is {lit}`cannot modify`), the column list, then the names of the query, then the number of
columns of the query against the number of columns to fill, then the {lit}`ON CONFLICT` clauses and
the {lit}`RETURNING` columns. The query sees no column of the written table. -/

namespace Belay.Sqlite.Model

/-- Resolve INSERT from a query as far as SQLite prepares it. Path 1 is the column list, path 2 the
query ({name}`resolveSelectDetailsTraced` below it, as for a {lit}`SELECT` statement), path 3 the
{lit}`ON CONFLICT` clauses and path 5 the {lit}`RETURNING` columns, as for {name}`resolveInsertTraced`. The
columns of the query are counted by its names, which a compound takes from its left-most term. The
counts, the repeated column of the list ({name}`RestrictionKind.insertColumnTwice`, because SQLite
accepts it and the model does not describe which value it stores), the policies of the conflict
algorithms and the restrictions of {name}`resolveInsertTraced` follow the same rules. A statement that
SQLite prepares is {name}`RestrictionKind.querySourceInsert`, until the model runs the rows. The trace
holds the table at path 0, then the names of the column list, of the query, of the clauses and of the
{lit}`RETURNING` columns, in the order in which the resolver reaches them. -/
def resolveInsertQueryTraced (context : ResolveContext) (catalog : Catalog) (tableName : Identifier)
    (names : Option (List Identifier)) (body : Syntax.SelectBody) (conflicts : List Syntax.ConflictClause)
    (algorithm : Option ConflictAlgorithm) (returning : List Syntax.ResultColumn) : TracedResolution :=
  let dqs := context.profile.dqsDml
  Traced.withTarget catalog tableName false
    (resolveViewTargetTraced context catalog tableName (Traced.lift (resolveViewModify catalog tableName)))
    (Traced.lift (prepareError catalog (.noSuchTable tableName))) fun position table =>
  let scope := Scope.singleAt (some position) tableName table.columns !table.withoutRowid
  if insertRowidTarget table names then Traced.lift (restrict [1] .rowidName) else
  Traced.stage catalog [1] ((insertPositionsTraced tableName table.columns scope names).mapError ValueIssue.prepare)
    fun positions =>
  Traced.sourceStage catalog ((resolveSelectDetailsTraced context catalog body.query body.subqueries).under [2])
    fun (source, _, _) =>
  let width := source.names.length
  if names.isNone && width != positions.length then
    Traced.lift (prepareError catalog (.expression (.valueCount tableName positions.length width)))
  else if names.isSome && width != positions.length then
    Traced.lift (prepareError catalog (.expression (.valuesForColumns width positions.length)))
  else if positions.eraseDups.length != positions.length then
    Traced.lift (restrict [1] .insertColumnTwice)
  else
  let keys := catalog.uniqueKeys position table
  Traced.stage catalog [3] (resolveAllTraced (resolveConflictTraced dqs tableName position table keys) conflicts)
    fun _ =>
  Traced.stage catalog [insertReturningField] (resolveReturningTraced dqs scope returning) fun _ =>
  let policy := catalog.writePolicy position table algorithm
  if policy.mixed then Traced.lift (restrict [] .mixedConflictAlgorithms)
  else if replacesDefault table policy then Traced.lift (restrict [] .replaceDefault)
  else Traced.lift (restrict [] .querySourceInsert)

end Belay.Sqlite.Model
