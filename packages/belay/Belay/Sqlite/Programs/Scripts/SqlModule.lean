import Belay.Sqlite.Frontend.Embedding.SqlModule
import Belay.Sqlite.Programs.Scripts.SqlFileForms

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Command Term

/-- Define one entry of the module as the script of its statement, with its documentation and
declaration range. Errors of the entry are logged, so the other entries are still defined. -/
def defineEntry (stx : Syntax) (file : LoadedSqlFile) (database : Option Database) (declName : Name)
    (entry : NamedEntry) : TermElabM Unit := do
  let (start, stop) := file.layout.statements[entry.statement]!
  let selection : FileSelection := { statements := #[entry.statement], replayStart := start, replayStop := stop }
  let chosen := file.chosen selection
  if let some database := database then file.logResolution stx database chosen (some entry.name)
  let value ← instantiateMVars (← fileScriptTerm stx file.source (file.replayText selection) chosen (some entry.name))
  let type ← Meta.inferType value
  let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
  let use ← currentSqlSourceUse file.source (some declName)
  modifyEnv (recordSqlSourceUse · use)
  addAndCompile <| .defnDecl { name := declName, levelParams := [], type := type, value := value,
                               hints := hints, safety := .safe }
  addDocStringCore declName (entryDocumentation file entry)
  addDeclarationRangesFromSyntax declName stx

end Belay.Sqlite
