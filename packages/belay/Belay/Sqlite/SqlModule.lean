import Belay.Sqlite.SqlFileSyntax

set_option doc.verso true

/-! {lit}`sql_module Queries from "sql/queries.sql"` (ADR 0017, S7): one definition for each
statement that a {lit}`-- name: id` marker names. Each definition is the script of its statement,
as {lit}`sql_file` would give for that statement's text, with the marker's documentation and
SQL location as its docstring. -/

namespace Belay.Sqlite

open Lean Elab Command Term

/-- {lit}`sql_module Queries from "sql/queries.sql"`: define {lit}`Queries.id` for each statement
that follows a {lit}`-- name: id` marker, with an optional ignored sqlc suffix such as {lit}`:one`.
The ordinary comment lines directly after the marker are the definition's documentation. A
statement without a name, an entry without exactly one statement, a duplicate name or a name
that is already declared is an error; a file with direction markers is refused. With
{lit}`(against := db)` each statement is checked against the database separately, so that no
statement sees another's schema changes. -/
syntax (name := sqlModuleCommand) "sql_module " ident " from " str (sqlFileAgainstOption)? : command

/-- The docstring of an entry: its documentation lines and its SQL location. -/
def entryDocumentation (file : LoadedSqlFile) (entry : NamedEntry) : String :=
  let lines := entry.marker.documentation ++ ["", s!"SQL source: {file.source.location entry.marker.start}"]
  "\n".intercalate lines

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
  addAndCompile <| .defnDecl { name := declName, levelParams := [], type := type, value := value,
                               hints := hints, safety := .safe }
  addDocStringCore declName (entryDocumentation file entry)
  addDeclarationRangesFromSyntax declName stx

/-- Elaborate {lit}`sql_module`: load and select the named entries, refuse names that already
exist before defining any, and define each entry. -/
@[command_elab sqlModuleCommand]
def elabSqlModule : CommandElab := fun stx => do
  let some path := stx[3].isStrLit? | throwUnsupportedSyntax
  let prefix_ := (← getCurrNamespace) ++ stx[1].getId
  runTermElabM fun _ => do
    let file ← loadSqlFile stx path
    let entries ← match selectNamed file.layout with
      | .error problem => file.fail stx problem
      | .ok entries => pure entries
    for entry in entries do
      if (← getEnv).contains (prefix_ ++ Name.mkSimple entry.name) then
        file.fail stx { range := some (entry.marker.start, entry.marker.stop), message :=
          s!"the name {prefix_ ++ Name.mkSimple entry.name} is already declared" } (some entry.name)
    let database ← match stx[4].getOptional? with
      | some option => evaluateDatabase option[1][2]
      | none => pure none
    for entry in entries do
      try defineEntry stx file database (prefix_ ++ Name.mkSimple entry.name) entry
      catch error => logException error

end Belay.Sqlite
