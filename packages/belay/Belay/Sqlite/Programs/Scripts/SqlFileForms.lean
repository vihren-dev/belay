import Belay.Sqlite.Schema.Dispatch.EvalDatabase
import Belay.Sqlite.Frontend.Embedding.SqlFileForms
import Belay.Sqlite.Programs.Scripts.Run
import Belay.Sqlite.Schema.Dispatch.SqlDiagnostics

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term

/-- The errors of the chosen statements against the catalog of the database, as {lit}`sql!` gives
them: each at the Lean form, with the SQL position. Statements resolve in order from the
database's catalog, so earlier schema changes of the script are visible to later ones. -/
def LoadedSqlFile.logResolution (file : LoadedSqlFile) (reference : Syntax) (database : Database)
    (chosen : Array Translation.ParameterizedStatement) (entry : Option String := none) : TermElabM Unit :=
  for diagnostic in scriptDiagnostics database.raw.connection.resolveState file.source.text.toUTF8
      (chosen.toList.map (·.statement)) do
    logErrorAt reference (file.source.diagnostic diagnostic entry)

end Belay.Sqlite
