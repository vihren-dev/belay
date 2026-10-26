import Belay.Sqlite.ReplayConstruction
import Belay.Sqlite.ProgramRun

set_option doc.verso true

/-! Replay the original SQL with SQLite shell bindings. Construction and parameter setup
can change connection counters, so this replay path requires statements to read neither a
clock nor counters. Other environments remain usable by certification and can yield unknown
replay. Every model step comes from the existing script runner. The witness that the replay reports
identifies the model execution that it follows: a statement with more than one possible execution
({name}`Belay.Sqlite.Model.RunStep.executions`) has no replay, because the report would have to
choose one execution for SQLite to confirm. -/

namespace Belay.Sqlite.Replay

open Lean Elab Term Meta
open Belay.Sqlite.Model

/-- The checked script value, its original SQL, and the parameter tokens recovered by
retranslation. Source text supplies spellings only; the actual bindings come from the value. -/
structure ScriptText where
  /-- The script whose statements and bindings passed kernel equality checking. -/
  value : Script
  /-- Original SQL text, before binding; query expressions are never replaced by answers. -/
  text : String
  /-- Translated statements with the original ranges and parameter names. -/
  items : Array Translation.ParameterizedStatement

/-- Match explicit or recovered SQL with an already checked script value. This function
checks syntax and recovers ranges; the caller is responsible for the value's equality with
its original expression. An explicit text supports hand-built script terms. -/
def scriptTextOf (expression : Expr) (value : Script) (text : Option String := none) : TermElabM ScriptText := do
  let source ← sourceOf scriptSourceKey expression
  let some text := text.or (source.map (·.text))
    | throwError "no original SQL is available for this script; supply its SQL text"
  let .ok items ← (translated text : IO _)
    | throwError "the supplied SQL cannot be translated for replay"
  if items.toList.map (·.statement.value) != value.statements.map (·.1) then
    throwError "the supplied SQL does not represent this script; supply the original SQL"
  return { value, text, items }

/-- Validate explicit or recovered SQL against a script's actual statement syntax. Rebinding
is retained because the value is evaluated from the complete supplied expression. -/
def scriptText (expression : Expr) (text : Option String := none)
    (excluded : Array Name := #[]) (excludedLocals : Array FVarId := #[]) : TermElabM ScriptText := do
  scriptTextOf expression (← scriptValue expression excluded excludedLocals) text

/-- Render SQLite shell bindings without rewriting the original query. The shell's parameter
table holds typed values; numeric slots use their assigned numbers and named slots retain
their signs. Missing values bind NULL, as in the model. -/
def bindingsSql (parameters : List Translation.Parameter) (values : List Value) : Option String := do
  if parameters.isEmpty then return ""
  let entries := parameters.foldl (fun found parameter =>
    let key := parameterKey parameter
    if found.any (fun (old, _) => old == key) then found
    else found ++ [(key, values.getD (parameter.number - 1) .null)]) []
  let inserts ← entries.mapM fun (key, value) => do
    let value ← valueLiteral value
    return "INSERT INTO temp.sqlite_parameters(key,value) VALUES ('" ++ key.replace "'" "''" ++
      "'," ++ value ++ ");\n"
  return "DELETE FROM temp.sqlite_parameters;\n" ++ String.join inserts

/-- Conservatively detect access to the SQLite shell's binding table. Scanning validated
SQL and construction text also covers trigger bodies. A mention in a comment or string can
refuse replay unnecessarily; certification and explicit database replay remain available. -/
def mentionsBindingTable (text : String) : Bool :=
  (text.toLower.splitOn "sqlite_parameters").length > 1

/-- Read environment dependencies and observations through the model's ordinary step.
The shell replay supports no clock/counter reads, including reads in subqueries and triggers.
An unmodeled step returns an unavailable result, never a native SQL failure. A statement with more
than one possible execution is unavailable too, because the shell's run is one execution. -/
def observations (database : Database) (script : Script) : Except String (List Output) := do
  let mut connection := database.raw.connection
  let mut outputs := []
  for ((statement, values), index) in script.statements.zipIdx do
    let step := runScriptStepWith (fun reason => Except.error reason)
      (fun resolved after clock run transition =>
        if resolved.readsClock || !resolved.counterReads.isEmpty then
          .error "replay of clock or connection-counter reads is unavailable"
        else .ok (ranScriptStep index values connection resolved after clock run transition))
      runContext none index connection statement values
    match ← step with
    | .ended reason => throw reason
    | .continued output next others =>
      unless others.isEmpty do
        throw s!"statement {index + 1} has more than one possible execution in the model, and the replay follows only one; write a statement that has one execution, or use the checked witness without replay"
      outputs := outputs ++ [output]; connection := next
  return outputs

/-- A replay whose construction and source match the checked values. Observations describe
the model, including every permitted result of a nondeterministic query; they are not a claim
that the shell has already run. No clock or counter is read by this replay's statements. -/
structure Report where
  /-- SQL that reconstructs the exact initial database. -/
  construction : String
  /-- Original SQL of the claim, retaining parameter references. None denotes a plain Lean predicate. -/
  original : Option String := none
  /-- Actual parameter values, in slot order for each statement. -/
  bindings : List (List Value) := []
  /-- Model observations. An unavailable model observation prevents this report. -/
  outputs : List Output := []
  /-- SQLite shell text: construction, bindings and original statements. -/
  sqlite : String

/-- Prepare the database-only replay for an arbitrary Lean predicate. It does not invent a
query for that predicate. The witness's logical refutation is checked separately. -/
def databaseReport (database : Expr) (text : Option String := none)
    (excluded : Array Name := #[]) (excludedLocals : Array FVarId := #[]) : TermElabM Report := do
  let (_, construction) ← Replay.construction database text excluded excludedLocals
  return { construction, sqlite := construction ++ "\n;\n" }

/-- Assemble a replay from previously checked construction, source and observations.
This formatter enforces the shell binding-table restriction and retains original statements;
constructing a report does not itself certify any of these inputs. -/
def render (construction : String) (source : ScriptText) (outputs : List Output) : TermElabM Report := do
  let bound := source.items.any (fun item => !item.parameters.isEmpty)
  if bound && (mentionsBindingTable construction || mentionsBindingTable source.text) then
    throwError "SQL replay is unavailable: the SQL can observe or change the shell binding table"
  let mut sqlite := ".bail off\n" ++ construction ++
    "\n;\nPRAGMA foreign_keys=OFF;\nPRAGMA recursive_triggers=OFF;\n" ++
    (if bound then ".parameter init\n" else "")
  for (item, (_, values)) in source.items.toList.zip source.value.statements do
    checkSystem "SQL replay formatting"
    let some bindings := bindingsSql item.parameters values
      | throwError "a parameter has no exact SQLite spelling; use a native SQLite value"
    let (start, stop) := statementRange item.statement
    let original := String.fromUTF8! (source.text.toUTF8.extract start stop)
    sqlite := sqlite ++ bindings ++ original ++ "\n;\n"
  return { construction
           original := some source.text
           bindings := source.value.statements.map (·.2)
           outputs, sqlite }

/-- Prepare a script replay from checked values and validated original text. Explicit text
inputs remain available for hand-built terms. The shell continues after SQL errors, matching
the script runner, and resets construction settings before the claim's statements. -/
def scriptReport (database script : Expr) (databaseText scriptSource : Option String := none)
    (excluded : Array Name := #[]) (excludedLocals : Array FVarId := #[]) : TermElabM Report := do
  let (value, construction) ← Replay.construction database databaseText excluded excludedLocals
  let source ← scriptText script scriptSource excluded excludedLocals
  let outputs ← match observations value source.value with
    | .ok outputs => pure outputs
    | .error reason => throwError "SQL replay is unavailable: {reason}"
  render construction source outputs

end Belay.Sqlite.Replay
