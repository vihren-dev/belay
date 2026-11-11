import Belay.Sqlite.Queries.Evaluation.SqlDocBindings
import Belay.Sqlite.Programs.Claims.SqlDocCheck
import Belay.Sqlite.Programs.Claims.SqlDocFailure
import Belay.Sqlite.Programs.Scripts.SqlDocInputs
import Belay.Sqlite.Frontend.Embedding.SqlDocBlock

set_option doc.verso true

namespace Belay.Sqlite.SqlDoc

open Lean Elab Term Belay.Sqlite Translation

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

end Belay.Sqlite.SqlDoc
