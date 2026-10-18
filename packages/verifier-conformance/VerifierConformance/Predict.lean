import VerifierConformance.Json

/-! The subject's side of ADR 0011's judge: predict what SQLite observes, without seeing it.

The input holds only the profile, the statement syntax of the starting schema and of the
script, and the starting rows by table name. The model resolves the syntax, runs the
resolved script, and reports each observed table in SQLite's catalog terms, the primary
SQLite result code and error phase that it predicts, each statement output, and whether the case is in the
model's scope. The judge, outside this repository's model code, compares the prediction
with the recorded observations. -/

open Lean

namespace Belay.Sqlite.Conformance

/-- The starting rows of one table, by its name in {lit}`sqlite_schema`. -/
structure NamedRows where
  name : String
  rows : List Row
  deriving FromJson

/-- What the model may see of a case: nothing that SQLite observed after the start. The
profile is the recorded one when the model implements its execution settings. -/
structure PredictInput where
  profile : Profile
  schema : List Syntax.Statement
  script : List Syntax.Statement
  initial : List NamedRows
  /-- The clock value of each statement, in SQLite's Julian-day milliseconds, as the judge
  supplies it; empty when the judge supplies none. -/
  clocks : List Int
  deriving FromJson

/-- A catalog column as {lit}`PRAGMA table_xinfo` reports it. Defaults retain
source spelling independently of their evaluated value. -/
def nativeColumn (column : CatalogColumn) : NativeColumn :=
  { name := column.name, declaredType := column.declaredType.getD "", notNull := column.notNull,
    defaultValue := column.defaultValue.map (·.sourceText) }

/-- The table at a catalog position, under its catalog object name, as native metadata. -/
def nativeTableOf (catalog : Catalog) (position : Nat) (name : String) (table : Table) : NativeTable where
  name := name
  columns := table.shape.columns.map nativeColumn
  primaryKey := table.shape.primaryKey
  uniqueKeys := table.shape.uniqueKeys
  indexes := catalogIndexes catalog position
  rows := table.rows

/-- The table at a catalog position in SQLite's catalog terms, whether its primary key
is the rowid, which decides whether SQLite makes an index for that key, and whether that
key is descending, which the index records. -/
def predictedTable (catalog : Catalog) (position : Nat) (table : Table) : Option Json :=
  catalog[position]?.map fun object => Json.mkObj [
    ("table", toJson (nativeTableOf catalog position object.name table)),
    ("rowidPrimaryKey", toJson table.shape.rowidAlias.isSome),
    ("primaryKeyDescending", toJson table.shape.primaryKeyDescending)]

/-- Starting rows as a native table without metadata: {name}`databaseOf` reads only
the name and the rows. -/
def NamedRows.native (table : NamedRows) : NativeTable where
  name := table.name
  columns := []
  primaryKey := []
  uniqueKeys := []
  indexes := []
  rows := table.rows

/-- Every table of one database, under its catalog, in catalog order. -/
def predictedTables (database : Database) : Json :=
  toJson ((List.range database.catalog.length).filterMap fun position =>
    (database.table position).bind (predictedTable database.catalog position))

/-- One predicted step: both databases, the transaction state and SQLite's primary
code. -/
def stepJson (observation : Observation) : Json :=
  Json.mkObj [("visible", predictedTables observation.visible),
    ("persisted", predictedTables observation.persisted),
    ("transactionOpen", toJson observation.transactionOpen),
    ("phase", toJson (errorPhase observation.error)),
    ("primaryCode", toJson (primaryCode observation.error))]

/-- The model's prediction. A model restriction puts the case out of scope. A schema
that resolution refuses although SQLite prepared it gives an empty initial step, which
the judge reports as a disagreement. Otherwise the case is in scope when the reached
statements pass the support check and none is unmodeled, the rule that
{name}`classifyCase` applies; each statement runs at its supplied clock value, and a script
that reads the clock is out of scope without clock values. -/
def predict (p : PredictInput) : Json :=
  let profile := p.profile
  match resolveSchemaAndScript profile p.schema p.script with
  | .error (.schemaRestricted restriction) | .error (.scriptRestricted restriction) =>
    Json.mkObj [("restricted", toJson restriction.reason), ("restriction", toJson restriction.kind.id)]
  | .error (.schemaPrepareError ..) =>
    Json.mkObj [("supported", toJson true), ("outputs", toJson ([] : List Json)), ("steps", toJson [
      Json.mkObj [("visible", toJson ([] : List Json)), ("persisted", toJson ([] : List Json)),
        ("transactionOpen", toJson false), ("primaryCode", toJson (0 : Nat)),
        ("phase", toJson (none : Option ErrorPhase))]])]
  | .ok unclocked =>
    let clock : Clock := fun position => p.clocks.getD position 0
    let resolution := { unclocked with resolved := scriptAtClock clock unclocked.resolved }
    let start : SqlState := { database := databaseOf resolution.startCatalog (p.initial.map NamedRows.native) }
    let pass := passFrom 0 resolution.resolved start
    let steps := pass.observations.map stepJson
    let supported := !(p.clocks.isEmpty && scriptReadsClock unclocked.resolved) &&
      pass.supported && !pass.observations.any invalidObservation
    Json.mkObj [("supported", toJson supported), ("steps", toJson steps), ("outputs", toJson pass.outputs)]

end Belay.Sqlite.Conformance
