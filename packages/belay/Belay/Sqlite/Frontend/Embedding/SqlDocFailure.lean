import Belay.Sqlite.Frontend.Embedding.DbDiagnostics

set_option doc.verso true

namespace Belay.Sqlite.SqlDoc

open Belay.Sqlite.Model

/-- Why a block stops at a statement. -/
inductive Stop where
  /-- The statement fails in SQLite. The diagnostic holds SQLite's message at its range of the
  SQL text, and the text is what the user can do next. -/
  | sqlFailure (diagnostic : Diagnostic) (action : String)
  /-- The model does not describe the statement, so the run ends. The diagnostic holds the
  reason at its range. -/
  | outsideModel (diagnostic : Diagnostic)

/-- The reason a block can give for a clock that the environment does not have. -/
def clockHint (reason : String) : String :=
  if reason == clockUnmodeled then
    s!"{reason}, or give the block a clock with (env := name) for a closed definition of the environment"
  else reason

end Belay.Sqlite.SqlDoc
