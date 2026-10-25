import Belay.Sqlite.SqlDocClosed
import Belay.Sqlite.SqlDocHeader
import Belay.Sqlite.SqlDocReport

set_option doc.verso true

/-! The closed inputs of a checked SQL documentation block: the database it starts from, the
environment, and the optional typed observation and explicit parameter values. Each is a
definition that the file or an import supplies, evaluated while the file elaborates. -/

namespace Belay.Sqlite.SqlDoc

open Lean Elab Term Belay.Sqlite

/-- A database exists, which the evaluation of a closed database needs. -/
local instance : Nonempty Database := ⟨Database.empty⟩

/-- An environment exists, which the evaluation of a closed environment needs. -/
local instance : Nonempty Env := ⟨Env.default⟩

/-- The evaluated closed inputs of a block. -/
structure Inputs where
  /-- The database that every run of the block starts from. -/
  database : Database
  /-- The clock and counters of the run; {name}`Env.default` when the header gives none. -/
  environment : Env
  /-- The complete typed observation from {lit}`(expected := name)`, if the header gives one. -/
  typedOutputs : Option (List Output)
  /-- The values of each statement from {lit}`(values := name)`, if the header gives them. -/
  explicitValues : Option (List (List Belay.Sqlite.Model.Value))

/-- Run an evaluation. An error is logged where Lean raised it and the result is absent, so that
one wrong input does not hide the others. -/
def attempt {α : Type} (action : TermElabM (Option α)) : TermElabM (Option α) := do
  try action catch error => do logException error; return none

/-- Evaluate the closed definition that an option names, or absent when the option is not
given or its evaluation failed. -/
def evaluateOption {α : Type} [Nonempty α] (option what : String) (type : Expr) (argument : Option Argument) :
    TermElabM (Option (Option α)) := do
  let some argument := argument | return some none
  let result ← attempt do
    let name ← definitionName option argument.value
    closedValue α what type name
  return result.map some

/-- Evaluate the inputs named by the header. The missing database is an error at the block, and
the other problems are errors at their arguments. The result is absent when any input is not
available, and no error follows from an input that Lean already rejects. -/
def evaluateInputs (source : BlockSource) (header : Header) : TermElabM (Option Inputs) := do
  if header.database.isNone then
    source.reportBlock "a SQL block needs the database it starts from; add (db := name) to the header, with the name of a closed Database definition, or (db := Database.empty) for a database without tables"
  let database ← evaluateOption "db" "database" (mkConst ``Database) header.database
  let environment ← evaluateOption "env" "environment" (mkConst ``Env) header.environment
  let typed ← evaluateOption "expected" "expected outputs" outputsType header.typedOutputs
  let explicit ← evaluateOption "values" "parameter values" valueListsType header.explicitValues
  match database, environment, typed, explicit with
  | some (some database), some environment, some typedOutputs, some explicitValues =>
    return some { database, environment := environment.getD Env.default, typedOutputs, explicitValues }
  | _, _, _, _ => return none

end Belay.Sqlite.SqlDoc
