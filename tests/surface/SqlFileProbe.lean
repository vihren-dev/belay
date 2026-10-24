import Belay
import Belay.Sqlite.SqlFileLoad
import Belay.Sqlite.SqlFileTerm

open Belay.Sqlite Lean Elab

/-! Test-only form for the source loader. Public sql_file waits for safe section handling. -/

/-- Exercise package discovery and the shared parameter constructor from a real Lake module. -/
elab "file_probe " path:str : term => do
  let source ← loadSqlFileSource path path.getString
  let items ← match ← (translateText source.text : IO _) with
    | .ok items => pure items
    | .error error => throwErrorAt path (source.diagnostic ⟨error.start, error.stop, error.message⟩)
  fileScriptTerm path source items
