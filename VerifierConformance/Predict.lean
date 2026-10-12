import VerifierConformance.Json

/-! The subject's side of ADR 0011's judge: predict what SQLite observes, without seeing it.

The input holds only the translated starting schema, the starting tables and the script.
The output holds the model's observation of the start and of each executed statement, the
primary SQLite result code that the model predicts, each statement output, and whether the
case is in the model's scope. The judge, outside this repository's model code, compares the
prediction with the recorded observations. -/

open Lean

namespace Belay.Sqlite.Conformance

/-- What the model may see of a case: nothing that SQLite observed after the start. -/
structure PredictInput where
  schema : Schema
  initial : FiniteDatabase
  script : List Statement
  deriving FromJson

/-- Every table name that the model can observe: the schema, the start and the script. -/
def PredictInput.names (p : PredictInput) : List String :=
  ((p.schema.map TableSchema.name) ++ p.initial.map Prod.fst ++ p.script.flatMap statementNames).eraseDups

/-- One predicted step: both table views, the transaction state and SQLite's primary code. -/
def stepJson (observation : Observation) : Json :=
  Json.mkObj [("visible", toJson observation.visible), ("persisted", toJson observation.persisted),
    ("transactionOpen", toJson observation.transactionOpen),
    ("primaryCode", toJson (primaryCode observation.error))]

/-- The model's prediction. A case is in scope when the schema and script are admitted and no
step fails with an invalid definition, the rule that `classifyCase` applies. -/
def predict (p : PredictInput) : Json :=
  let start : SqlState := { database := databaseOf p.initial }
  let observed := trace p.names p.script start.database
  let supported := schemaAllows p.schema p.script && supportedSqlFrom 0 p.script start &&
    !observed.any invalidObservation
  Json.mkObj [("supported", toJson supported), ("steps", toJson (observed.map stepJson)),
    ("outputs", toJson (outputTraceFrom 0 p.script start))]

end Belay.Sqlite.Conformance
