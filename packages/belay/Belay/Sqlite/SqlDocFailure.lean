import Belay.Sqlite.DbDiagnostics
import Belay.Sqlite.ProgramRun
import Belay.Sqlite.SqlDocObservation

set_option doc.verso true

/-! The first statement of a checked SQL documentation block that does not return a result:
an SQL failure, or a statement outside the model. The message uses the actual values bound to
the statement and the actual clock, and the connection as the earlier statements left it. The
model's run supplies all behavior; this module only finds the statement and asks for its
message. -/

namespace Belay.Sqlite.SqlDoc

open Belay.Sqlite.Model Translation

/-- Why a block stops at a statement. -/
inductive Stop where
  /-- The statement fails in SQLite. The diagnostic holds SQLite's message at its range of the
  SQL text, and the text is what the user can do next. -/
  | sqlFailure (diagnostic : Diagnostic) (action : String)
  /-- The model does not describe the statement, so the run ends. The diagnostic holds the
  reason at its range. -/
  | outsideModel (diagnostic : Diagnostic)

/-- The position of the first output that is an error or outside the model, if there is one. -/
def firstStop? (outputs : List Output) : Option Nat :=
  outputs.findIdx? fun
    | .error _ | .unmodeled _ => true
    | .rows _ | .done _ | .oneOf _ => false

/-- The reason a block can give for a clock that the environment does not have. -/
def clockHint (reason : String) : String :=
  if reason == clockUnmodeled then
    s!"{reason}, or give the block a clock with (env := name) for a closed definition of the environment"
  else reason

/-- Explain the output at the position of the script: the message of the failed statement for the
connection that the earlier statements leave, with the values of the statement and the clock of the
environment, or the reason that the model gives for the statement. The statements are those
that translation gave, and the script holds their values. -/
def explainStop (bytes : ByteArray) (database : Database) (environment : Env)
    (items : Array ParameterizedStatement) (script : Script) (outputs : List Output) (index : Nat) :
    Option Stop := do
  let item := (items[index]?.map (·.statement))
  let item ← item
  let (_, values) ← script.statements[index]?
  let connection := (runScriptFrom runContext environment.clock 0 (database.raw.connection environment.counters)
    (script.statements.take index)).connection
  match outputs[index]? with
  | some (.error code) =>
    let (diagnostic, action) := failureParts environment.clock bytes index connection item values code
    some (.sqlFailure diagnostic action)
  | some (.unmodeled reason) =>
    let diagnostic := endedDiagnostic connection item (clockHint reason)
    some (.outsideModel diagnostic)
  | some (.rows _) | some (.done _) | some (.oneOf _) | none => none

end Belay.Sqlite.SqlDoc
