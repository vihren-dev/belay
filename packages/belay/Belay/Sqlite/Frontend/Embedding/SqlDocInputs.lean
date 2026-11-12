import Belay.Sqlite.Frontend.Embedding.SqlDocClosed
import Belay.Sqlite.Frontend.Embedding.SqlDocHeader
import Belay.Sqlite.Frontend.Embedding.SqlDocReport

set_option doc.verso true

namespace Belay.Sqlite.SqlDoc

open Lean Elab Term Belay.Sqlite

/-- Run an evaluation. An error is logged where Lean raised it and the result is absent, so that
one wrong input does not hide the others. -/
def attempt {α : Type} (action : TermElabM (Option α)) : TermElabM (Option α) := do
  try action catch error => do logException error; return none

end Belay.Sqlite.SqlDoc
