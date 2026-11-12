import Belay.Sqlite.Tooling.SqlCommands.SqlDocInputs
import Belay.Sqlite.Programs.Claims.SqlDocBlock

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
