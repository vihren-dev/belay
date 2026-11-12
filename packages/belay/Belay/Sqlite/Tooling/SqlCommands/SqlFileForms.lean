import Belay.Sqlite.Tooling.Counterexamples.EvalDatabase
import Belay.Sqlite.Programs.Scripts.SqlFileForms

set_option doc.verso true

/-! What {lit}`sql_file` and {lit}`sql_module` share (ADR 0017, S7): loading and translating a
file once, choosing statements from it, and checking them against a database with the errors of
{lit}`sql!`. Each error is raised at the Lean form and names the SQL file, line and column. -/

namespace Belay.Sqlite

open Lean Elab Term

/-- Check the chosen statements against the value of the database term, once. A database with
its own error shows that error and gives no extra diagnostics here. -/
def LoadedSqlFile.checkAgainst (file : LoadedSqlFile) (reference databaseTerm : Syntax)
    (chosen : Array Translation.ParameterizedStatement) : TermElabM Unit := do
  if let some database ← evaluateDatabase databaseTerm then
    file.logResolution reference database.value chosen

end Belay.Sqlite
