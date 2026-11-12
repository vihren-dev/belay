import Belay.Sqlite.Tooling.SqlCommands.SqlFileSyntax
import Belay.Sqlite.Programs.Scripts.SqlModule

set_option doc.verso true

/-! {lit}`sql_module Queries from "sql/queries.sql"` (ADR 0017, S7): one definition for each
statement that a {lit}`-- name: id` marker names. Each definition is the script of its statement,
as {lit}`sql_file` would give for that statement's text, with the marker's documentation and
SQL location as its docstring. -/

namespace Belay.Sqlite

open Lean Elab Command Term

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
          s!"the name {prefix_ ++ Name.mkSimple entry.name} is already declared; rename the SQL entry, or choose another module name" } (some entry.name)
    let database ← match stx[4].getOptional? with
      | some option => pure ((← evaluateDatabase option[1][2]).map (·.value))
      | none => pure none
    for entry in entries do
      try defineEntry stx file database (prefix_ ++ Name.mkSimple entry.name) entry
      catch error => logException error

end Belay.Sqlite
