import Belay.Sqlite.SqlTerm
import Belay.Sqlite.SqlFileDiagnostics

set_option doc.verso true

namespace Belay.Sqlite
open Lean Elab Term

/-- Construct whole-file statements as an ordinary script function. Every
parameter, including dollar names, is an explicit argument. The shared planner keeps original
SQLite identities and sparse slots. Diagnostics use the full external file's coordinates.
The unchanged file text must contain exactly these statements for source replay. A caller
that selects a section or named entry needs separate replay text and full-file coordinates. -/
def fileScriptTerm (reference : Syntax) (source : SqlFileSource)
    (items : Array Translation.ParameterizedStatement) (entry : Option String := none) : TermElabM Expr := do
  let plan ← match planParameters (items.toList.map (·.parameters)) .file with
    | .ok plan => pure plan
    | .error diagnostic => throwErrorAt reference (source.diagnostic diagnostic entry)
  let fileName ← getFileName
  scriptTermFromPlan items plan [] (withSource scriptSourceKey reference source.text fileName)

end Belay.Sqlite
