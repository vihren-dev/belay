import VerifierConformance.PredictTables

/-! The subject's side of ADR 0011's judge: predict what SQLite observes, without seeing it.

The input holds only the profile, the statement syntax of the starting schema and of the
script, the starting rows by table name, the counters of the connection when the record has
them, and the clock values and the values bound to the parameters of each executed statement. The model resolves the syntax, runs the resolved script
with them, and reports each observed table in SQLite's catalog terms, the primary
SQLite result code and error phase that it predicts, each statement output, and whether the case is in the
model's scope. The judge, outside this repository's model code, compares the prediction
with the recorded observations. -/

open Lean

namespace Belay.Sqlite.Model.Conformance

/-- The starting rows of one table, by its name in {lit}`sqlite_schema`. -/
structure NamedRows where
  name : Identifier
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
  /-- The values bound to the parameters of each executed statement, as the judge supplies
  them; empty when the judge supplies none, so that each statement binds no values. -/
  parameters : List (List Value)
  /-- Whether the recorder ran on after an SQL error (native record version 6), so that the
  prediction comes from the model's run that continues ({name}`runPassFrom`); false for a
  recorder that stops at the first error. -/
  continues : Bool
  /-- The counters of the connection just before the migration runs (native record version 7),
  as the judge supplies them; none when the judge supplies none, so that the run starts with
  unknown counters. -/
  counters : Option Counters
  deriving FromJson

/-- Starting rows as a native table without metadata: {name}`databaseOf` reads only
the name and the rows. -/
def NamedRows.native (table : NamedRows) : NativeTable where
  name := table.name
  columns := []
  primaryKey := []
  uniqueKeys := []
  indexes := []
  rows := table.rows

/-- The prediction of a model restriction: the case is out of scope, with the reason and the
kind of the restriction. -/
def restrictedJson (restriction : Restriction) : Json :=
  Json.mkObj [("restricted", toJson restriction.reason), ("restriction", toJson restriction.kind.id)]

/-- The prediction of a schema that resolution refuses although SQLite prepared it: an empty
initial step, which the judge reports as a disagreement. -/
def refusedSchemaJson : Json :=
  Json.mkObj [("supported", toJson true), ("outputs", toJson ([] : List Json)), ("steps", toJson [
    Json.mkObj [("visible", toJson ([] : List Json)), ("persisted", toJson ([] : List Json)),
      ("transactionOpen", toJson false), ("primaryCode", toJson (0 : Nat)),
      ("phase", toJson (none : Option ErrorPhase))]])]

/-- The prediction of a case whose recorder stops at the first error. A model restriction puts
the case out of scope ({name}`restrictedJson`), and a schema that resolution refuses although
SQLite prepared it gives {name}`refusedSchemaJson`. Otherwise the case is in scope when the
reached statements pass the support check and none is unmodeled, the rule that
{name}`classifyHaltingCase` applies; each statement runs at its supplied clock value, and a
script that reads the clock is out of scope without clock values. -/
def predictHalting (p : PredictInput) : Json :=
  match resolveSchemaAndScript p.profile p.schema p.script with
  | .error (.schemaRestricted restriction) | .error (.scriptRestricted restriction) => restrictedJson restriction
  | .error (.schemaPrepareError ..) => refusedSchemaJson
  | .ok resolution =>
    let clock : Clock := fun position => p.clocks.getD position 0
    let start : SqlState := { database := databaseOf resolution.startCatalog (p.initial.map NamedRows.native),
                              clock := scriptClock clock resolution.resolved, counters := p.counters.getD {} }
    let pass := passFrom 0 (bindValues resolution.resolved p.parameters) start
    let steps := predictionSteps p.profile p.clocks pass.counters pass.observations
    let supported := !(p.clocks.isEmpty && scriptReadsClock resolution.resolved) &&
      pass.supported && !pass.observations.any invalidObservation
    match steps with
    | .error issue => observationIssueJson issue
    | .ok steps =>
      Json.mkObj [("supported", toJson supported), ("steps", toJson steps), ("outputs", toJson pass.outputs)]

/-- The prediction of a case whose recorder runs on after an SQL error, the rule that
{name}`classifyRunCase` applies: the schema resolves as in {name}`predictHalting`, then the
model's run that continues ({name}`runPassFrom`) gives the observation after each statement and
its output. A statement that ends the run puts the case out of scope. -/
def predictRun (p : PredictInput) : Json :=
  match resolveSchema p.profile p.schema with
  | .error (.schemaRestricted restriction) | .error (.scriptRestricted restriction) => restrictedJson restriction
  | .error (.schemaPrepareError ..) => refusedSchemaJson
  | .ok catalog =>
    let connection := startConnection p.profile catalog (p.initial.map NamedRows.native) p.counters
    let pass := runPassFrom { profile := p.profile, mode := .execution } (runClock p.clocks) 0 connection
      (bindValues p.script p.parameters)
    let observations := observeState connection.state :: pass.observations
    let supported := pass.supported && !observations.any invalidObservation
    match predictionSteps p.profile p.clocks (connection.state.counters :: pass.counters) observations with
    | .error issue => observationIssueJson issue
    | .ok steps =>
      Json.mkObj [("supported", toJson supported), ("steps", toJson steps), ("outputs", toJson pass.outputs)]

/-- The model's prediction: {name}`predictRun` for a case whose recorder ran on after an error
({lit}`PredictInput.continues`), and {name}`predictHalting` otherwise. -/
def predict (p : PredictInput) : Json :=
  if p.continues then predictRun p else predictHalting p

end Belay.Sqlite.Model.Conformance
