import VerifierConformance.Json
import VerifierConformance.ViewObservation

set_option doc.verso true

/-! The subject's catalog observations. Physical tables retain their stored rows; views
use the same resolved query and execution as an application SELECT. -/

open Lean

namespace Belay.Sqlite.Model.Conformance

/-- A catalog column as {lit}`PRAGMA table_xinfo` reports it. Defaults retain
source spelling independently of their evaluated value. -/
def nativeColumn (column : CatalogColumn) : NativeColumn :=
  { name := column.name, declaredType := column.declaredType.getD "", notNull := column.notNull,
    defaultValue := column.defaultValue.map (·.sourceText), hidden := columnHidden column }

/-- The table at a catalog position, under its catalog object name, as native metadata. -/
def nativeTableOf (catalog : Catalog) (position : Nat) (name : Identifier) (table : Table) : NativeTable where
  name := name
  columns := table.shape.columns.map nativeColumn
  primaryKey := table.shape.primaryKey
  uniqueKeys := table.shape.uniqueKeys
  indexes := catalogIndexes catalog position
  rows := table.rows
  withoutRowid := table.shape.withoutRowid

/-- A foreign key of a table in the terms of {lit}`PRAGMA foreign_key_list`: the referenced
table, the names of its columns, the referenced columns, and the names of its actions. -/
def foreignKeyJson (columns : List CatalogColumn) (key : ForeignKey) : Json :=
  Json.mkObj [("table", toJson key.table),
    ("columns", toJson (key.columns.filterMap fun position => columns[position]?.map (·.name))),
    ("referenced", toJson key.referenced), ("onDelete", toJson key.onDelete.sqlName),
    ("onUpdate", toJson key.onUpdate.sqlName)]

/-- The table at a catalog position in SQLite's catalog terms, whether its primary key
is the rowid, which decides whether SQLite makes an index for that key, whether that
key is descending, which the index records, the collation name of each column, which
the indexes of the primary key and of UNIQUE constraints record, and its foreign keys in
the order in which SQLite creates them ({name}`CatalogTable.allForeignKeys`).
{lit}`collations` and {lit}`foreignKeys` are present only when a column is not
{lit}`BINARY` or the table has a foreign key, so other predictions keep their form. -/
def predictedTable (catalog : Catalog) (position : Nat) (table : Table) : Option Json :=
  let collations := collationNames (table.shape.columns.map (·.collation.sqlName))
  let foreignKeys := table.shape.allForeignKeys.map (foreignKeyJson table.shape.columns)
  catalog[position]?.map fun object => Json.mkObj ([
    ("table", toJson (nativeTableOf catalog position object.name table)),
    ("rowidPrimaryKey", toJson table.shape.rowidAlias.isSome),
    ("primaryKeyDescending", toJson table.shape.primaryKeyDescending)] ++
    (if collations.isEmpty then [] else [("collations", toJson collations)]) ++
    (if foreignKeys.isEmpty then [] else [("foreignKeys", toJson foreignKeys)]))

/-- A view that SQLite cannot read, with the primary result code of its failure
({name}`ViewObservationIssue.failureCode`). A recording keeps such a view with that code and
its message, and the judge compares the code. -/
def unreadableViewJson (name : Identifier) (code : Nat) : Json :=
  Json.mkObj [("kind", toJson "view"),
    ("unreadable", Json.mkObj [("name", toJson name), ("primaryCode", toJson code)])]

/-- All observable catalog tables and views, in catalog order. A view has no stored rows;
its native rows and metadata come from {name}`observeView`. A view that fails as SQLite
reports it is an unreadable view ({name}`unreadableViewJson`); an unmodeled view stops this
observation explicitly instead of supplying an empty table. -/
def predictedTables (profile : Profile) (clock : Option Int) (counters : Counters)
    (database : Database) : Except ViewObservationIssue Json := do
  let tables ← database.catalog.zipIdx.filterMapM fun (object, position) =>
    match object.entry with
    | .table _ => pure ((database.table position).bind (predictedTable database.catalog position))
    | .view _ =>
      match observeView profile clock counters database object.name with
      | .ok view => pure (some (Json.mkObj [("table", toJson view), ("kind", toJson "view"),
          ("rowidPrimaryKey", toJson false), ("primaryKeyDescending", toJson false)]))
      | .error issue => match issue.failureCode with
        | some code => pure (some (unreadableViewJson object.name code))
        | none => throw (.named object.name issue)
    | .index _ | .trigger _ => pure none
  pure (toJson tables)

/-- One snapshot with its actual writer counters and supplied observation clock.
Outside a transaction both observations use the writer. Inside one, the committed
snapshot uses the native recorder's separate read-only-in-practice connection, whose
counters start at zero and remain unchanged by its catalog queries. -/
def stepJson (profile : Profile) (clock : Option Int) (counters : Counters)
    (observation : Observation) : Except ViewObservationIssue Json := do
  let visible ← predictedTables profile clock counters observation.visible
  let persisted ← if observation.transactionOpen then
      predictedTables profile clock Counters.newConnection observation.persisted else pure visible
  pure (Json.mkObj [("visible", visible), ("persisted", persisted),
    ("transactionOpen", toJson observation.transactionOpen),
    ("phase", toJson (errorPhase observation.error)),
    ("primaryCode", toJson (primaryCode observation.error))])

/-- Observe a pass with its aligned writer counters. The initial snapshot uses the clock of the
setup and each later snapshot the clock of its statement. Missing clock and counter inputs
stay unknown. -/
def predictionSteps (profile : Profile) (setupClock : Option Int) (clocks : List Int)
    (counters : List Counters) (observations : List Observation) :
    Except ViewObservationIssue (List Json) :=
  observations.zipIdx.mapM fun (observation, index) =>
    stepJson profile (if index == 0 then setupClock else clocks[index - 1]?)
      (counters.getD index {}) observation

/-- The text " in view NAME" for an error message, or nothing without a view. -/
def viewSuffix : Option Identifier → String
  | some name => s!" in view {name.text}"
  | none => ""

/-- The advice that ends the error text of a view that SQLite cannot read. -/
def repairAdvice : String := "Change the view or drop it, so that the statement can read it."

/-- Report an unavailable observation of the view {lit}`view`, if known. A model restriction or
unmodeled output is out of scope. An SQL preparation or execution error normally becomes an
unreadable view ({name}`unreadableViewJson`) before it reaches this report; the error text
remains for an issue that arrives without that conversion, and is never an empty snapshot or a
model restriction. Each error text names the view and says how to repair it. -/
def observationIssueAt (view : Option Identifier) : ViewObservationIssue → Json
  | .named name issue => observationIssueAt (some name) issue
  | .resolution (.value (.restriction _ kind)) =>
    Json.mkObj [("restricted", toJson kind.message), ("restriction", toJson kind.id)]
  | .resolution (.value (.prepare error)) =>
    Json.mkObj [("error", toJson (s!"view observation prepare error{viewSuffix view}: {error.message}. " ++ repairAdvice))]
  | .resolution (.noSuchTable name) =>
    Json.mkObj [("error", toJson (s!"view observation prepare error{viewSuffix view}: no such table: {name.text}. " ++ repairAdvice))]
  | .output (.unmodeled reason) =>
    Json.mkObj [("restricted", toJson s!"view observation{viewSuffix view}: {reason}")]
  | .output (.error code) =>
    Json.mkObj [("error", toJson (s!"view observation execution error{viewSuffix view}: code {code}. " ++ repairAdvice))]
  | .output (.rows _) | .output (.oneOf _) | .output (.done _) | .shape =>
    Json.mkObj [("error", toJson s!"view observation has an unexpected query shape or output{viewSuffix view}. Report this case.")]

/-- Report an unavailable observation whose view is named by the issue, if known
({name}`observationIssueAt`). -/
def observationIssueJson (issue : ViewObservationIssue) : Json := observationIssueAt none issue

end Belay.Sqlite.Model.Conformance
