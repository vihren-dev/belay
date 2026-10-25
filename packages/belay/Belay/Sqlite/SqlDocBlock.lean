import Belay.Sqlite.SqlDocBindings
import Belay.Sqlite.SqlDocCheck
import Belay.Sqlite.SqlDocComments
import Belay.Sqlite.SqlDocFailure
import Belay.Sqlite.SqlDocInputs
import Belay.Sqlite.SqlTerm

set_option doc.verso true

/-! The {lit}`sql` code block of a Lean docstring, checked while the file elaborates. With
{lit}`set_option doc.verso true`, a block such as the following runs its SQL on the database
that {lit}`(db := name)` names and compares what the statements return with the {lit}`--` lines at
the end of the block:

{lit}`sql (db := start)`, then the SQL {lit}`UPDATE t SET x = 7; SELECT x FROM t;`, then the line
{lit}`-- 7`. The header options are {lit}`db`, {lit}`env`, {lit}`values` and {lit}`expected`,
and the flag {lit}`+error`; every other named argument binds the parameter of its name. The
walkthrough with checked examples is the documentation of {lit}`Belay.Sqlite.SqlDocGuide`. -/

namespace Belay.Sqlite.SqlDoc

open Lean Elab Term Belay.Sqlite Translation

/-- The syntax where a problem is shown. -/
def problemReference (header : Header) : Place → Option Syntax
  | .sql _ _ => none
  | .header "values" => header.explicitValues.map (·.reference)
  | .header name => (header.bindings.find? (·.name == name)).map (·.reference)

/-- Log each problem at its SQL token or its header argument. -/
def reportProblems (source : BlockSource) (header : Header) (problems : List Problem) : TermElabM Unit :=
  for problem in problems do
    match problem.place with
    | .sql start stop => source.reportSql start stop problem.message
    | place => logErrorAt ((problemReference header place).getD source.block) problem.message

/-- The script of the statements with the values of their parameters, or absent after the
problems of the bindings are logged. The explicit list and the named arguments exclude each other. -/
def bindScript (source : BlockSource) (header : Header) (inputs : Inputs)
    (items : Array ParameterizedStatement) : TermElabM (Option Script) := do
  let statements := items.toList.map (·.parameters)
  let plain : Script := ⟨items.toList.map fun item => (item.statement.value, [])⟩
  match inputs.explicitValues with
  | some lists =>
    for binding in header.bindings do
      logErrorAt binding.reference s!"the header argument {binding.name} cannot be used with (values := ...), which binds every parameter by number; remove one of them"
    let problems := explicitProblems statements lists
    reportProblems source header problems
    return if header.bindings.isEmpty && problems.isEmpty then some (plain.withValues lists) else none
  | none =>
    match namedPlan statements (header.bindings.map (·.name)) with
    | .error problems => reportProblems source header problems; return none
    | .ok plan =>
      let mut values : List (String × Belay.Sqlite.Model.Value) := []
      for binding in header.bindings do
        match ← attempt (valueOfArgument binding.value) with
        | some value => values := values ++ [(binding.name, value)]
        | none => return none
      return some (plain.withValues (planValues plan (fun name => values.lookup name)))

/-- The message when an expected failure compares to a different one. -/
def errorMismatch (expected actual : String) : String :=
  s!"SQL error mismatch\nexpected message: {repr expected}\nactual message: {repr actual}\n\
    Correct the SQL, or write the actual message in the comment lines at the end of the block"

/-- Run the script and compare it with the block's expectation. The first statement that fails
or is outside the model ends the check: with {lit}`+error` an SQL failure is compared with the
expected message, and every other case is an error at the statement. -/
def runAndCompare (source : BlockSource) (header : Header) (inputs : Inputs)
    (items : Array ParameterizedStatement) (script : Script) (text : String) : TermElabM Unit := do
  let outputs := (inputs.database.run script inputs.environment).outputs
  let expectedText := expectedComments text
  let expectation := match inputs.typedOutputs with
    | some typed => Expectation.outputs typed
    | none => Expectation.text expectedText
  match firstStop? outputs with
  | some index =>
    match explainStop text.toUTF8 inputs.database inputs.environment items script outputs index with
    | some (.sqlFailure diagnostic action) =>
      if header.expectsError then
        unless diagnostic.message == expectedText do
          source.reportBlock (errorMismatch expectedText diagnostic.message)
      else
        source.reportSql diagnostic.start diagnostic.stop
          s!"{diagnostic.message}{action}. To show this failure in the documentation, add +error to the header"
    | some (.outsideModel diagnostic) => source.reportSql diagnostic.start diagnostic.stop diagnostic.message
    | none => source.reportBlock s!"the model gives no explanation for statement {index + 1}; report the SQL to the maintainers of the model"
  | none =>
    if header.expectsError then
      source.reportBlock "the SQL ran without an error, and the header has +error; remove +error, or change the SQL so that a statement fails"
    else match checkOutputs expectation outputs with
      | .ok () => pure ()
      | .error failure => source.reportBlock failure.message

/-- Check one {lit}`sql` code block: read the header, evaluate its closed inputs, translate the
text, bind the parameters, run the script and compare. Every problem is an error at the argument
or SQL occurrence that the user changes. A block with a wrong header is not run. A syntax or
preparation error that translation finds is an expected failure with {lit}`+error`. -/
def checkBlock (code : StrLit) (arguments : Array (TSyntax `doc_arg)) : TermElabM Unit := do
  let source ← BlockSource.ofBlock code
  let header ← parseHeader arguments
  for (reference, message) in header.problems do logErrorAt reference message
  if let some typed := header.typedOutputs then
    if header.expectsError then
      logErrorAt typed.reference "(expected := ...) states the outputs of a block that succeeds, and +error expects a failure; remove one of them"
      return
  unless header.problems.isEmpty do return
  let inputs ← evaluateInputs source header
  let text := code.getString
  match ← (translateText text : IO _) with
  | .error refusal =>
    let stop := max refusal.stop (refusal.start + 1)
    if refusal.status == "INPUT_ERROR" && header.expectsError then
      let expected := expectedComments text
      unless refusal.message == expected do source.reportBlock (errorMismatch expected refusal.message)
    else source.reportSql refusal.start stop refusal.message
  | .ok items =>
    let some inputs := inputs | return
    let some script ← bindScript source header inputs items | return
    runAndCompare source header inputs items script text

/-- The {lit}`sql` code block expander, which checks the block and keeps its text for rendering. -/
def expandSql : Doc.DocCodeBlockExpander := fun code => do
  let arguments ← get
  set (#[] : Array (TSyntax `doc_arg))
  checkBlock code arguments
  return .code code.getString

initialize Doc.addBuiltinDocCodeBlock `sql ``expandSql expandSql

end Belay.Sqlite.SqlDoc
