import Belay.Sqlite.SqlFileForms

set_option doc.verso true

/-! {lit}`sql_file "path"` (ADR 0017, S7): the script of an SQL file of the package, as
{lit}`sql` gives it for the same text. A file with goose or dbmate direction markers needs a
{lit}`(section := "up")` or {lit}`"down"`. {lit}`(against := db)` checks the statements against
the database as {lit}`sql!` does, without changing the script. -/

namespace Belay.Sqlite

open Lean Elab Term

/-- The setting {lit}`section := "up"` of {lit}`sql_file`. -/
syntax sqlFileSection := &"section" " := " str

/-- The setting {lit}`against := db` of {lit}`sql_file` and {lit}`sql_module`. -/
syntax sqlFileAgainst := &"against" " := " term

/-- A parenthesized setting of {lit}`sql_file`. The parenthesis is shared by both settings, so
that a second setting after the first parses. -/
syntax sqlFileOption := " (" (sqlFileSection <|> sqlFileAgainst) ")"

/-- The parenthesized {lit}`(against := db)` of {lit}`sql_module`. -/
syntax sqlFileAgainstOption := " (" sqlFileAgainst ")"

/-- {lit}`sql_file "sql/schema.sql"`: the script of the statements of the file, whose path is
relative to the package that owns the Lean source. Parameters, including {lit}`$name`, are
arguments of type {lit}`Value`, in the order of first appearance. A file with migration direction
markers is selected with {lit}`(section := "up")` or {lit}`(section := "down")`. The file is
read and translated while the Lean file elaborates; an edit to it needs a rebuild, or a restart
of the Lean file in the editor. -/
syntax (name := sqlFileTerm) "sql_file " str sqlFileOption* : term

/-- The options of a {lit}`sql_file` form: at most one section and one database. -/
private def fileOptions (options : Array Syntax) : TermElabM (Option Syntax × Option Syntax) := do
  let mut section_ := none
  let mut against := none
  for option in options do
    let setting := option[1]
    if setting.getKind == ``sqlFileSection then
      if section_.isSome then throwErrorAt option "the section is given twice"
      section_ := some setting[2]
    else
      if against.isSome then throwErrorAt option "the database is given twice"
      against := some setting[2]
  return (section_, against)

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
