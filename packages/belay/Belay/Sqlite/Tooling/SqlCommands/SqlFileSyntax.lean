import Belay.Sqlite.Tooling.SqlCommands.SqlFileForms
import Belay.Sqlite.Frontend.Embedding.SqlFileSyntax

set_option doc.verso true

/-! {lit}`sql_file "path"` (ADR 0017, S7): the script of an SQL file of the package, as
{lit}`sql` gives it for the same text. A file with goose or dbmate direction markers needs a
{lit}`(section := "up")` or {lit}`"down"`. {lit}`(against := db)` checks the statements against
the database as {lit}`sql!` does, without changing the script. -/

namespace Belay.Sqlite

open Lean Elab Term

/-- Elaborate {lit}`sql_file`: load the file, select its statements, check them against the
database when one is given, and build the script. -/
@[term_elab sqlFileTerm]
def elabSqlFile : TermElab := fun stx _ => do
  let some path := stx[1].isStrLit? | throwUnsupportedSyntax
  let (section_, against) ← fileOptions stx[2].getArgs
  let file ← loadSqlFile stx path
  let selection ← match section_ with
    | none => match selectWholeFile file.layout with
      | .error problem => file.fail stx problem
      | .ok selection => pure selection
    | some literal =>
      let some name := literal.isStrLit? | throwUnsupportedSyntax
      match parseSection name with
      | .error problem => throwErrorAt literal (file.source.problem problem)
      | .ok direction => match selectSection file.layout direction with
        | .error problem => file.fail stx problem
        | .ok selection => pure selection
  let chosen := file.chosen selection
  if let some database := against then file.checkAgainst stx database chosen
  fileScriptTerm stx file.source (file.replayText selection) chosen

end Belay.Sqlite
