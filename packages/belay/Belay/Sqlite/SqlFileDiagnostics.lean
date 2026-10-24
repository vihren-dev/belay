import Belay.Sqlite.SqlFileSource
import Belay.Sqlite.SqlDiagnostics

set_option doc.verso true

namespace Belay.Sqlite
open Lean

/-- Render an external SQL diagnostic with its original one-based line and character column.
UTF-8 byte offsets come from the parser; Lean's file map counts Unicode characters. The Lean
form remains the diagnostic's location, while this message identifies the SQL file and entry. -/
def SqlFileSource.diagnostic (source : SqlFileSource) (diagnostic : Diagnostic)
    (entry : Option String := none) : String :=
  let position := (FileMap.ofString source.text).toPosition ⟨min diagnostic.start source.text.utf8ByteSize⟩
  let statement := entry.map (fun name => s!"in statement `{name}`: ") |>.getD ""
  s!"{source.path}:{position.line}:{position.column + 1}: {statement}{diagnostic.message}"

end Belay.Sqlite
