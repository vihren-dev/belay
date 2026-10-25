import Belay.Sqlite.SqlTerm
import Belay.Sqlite.SqlFileDiagnostics

set_option doc.verso true

namespace Belay.Sqlite
open Lean Elab Term

/-- Construct whole-file statements as an ordinary script function. Every
parameter, including dollar names, is an explicit argument. The shared planner keeps original
SQLite identities and sparse slots. Diagnostics use the full external file's coordinates.
The replay text must contain exactly these statements: the whole file, or the selected
section or entry, while diagnostics keep the whole file's coordinates. -/
def fileScriptTerm (reference : Syntax) (source : SqlFileSource) (replayText : String)
    (items : Array Translation.ParameterizedStatement) (entry : Option String := none) : TermElabM Expr := do
  let plan ← match planParameters (items.toList.map (·.parameters)) .file with
    | .ok plan => pure plan
    | .error diagnostic => throwErrorAt reference (source.diagnostic diagnostic entry)
  let fileName ← getFileName
  scriptTermFromPlan items plan [] none (withSource scriptSourceKey reference replayText fileName)

end Belay.Sqlite
