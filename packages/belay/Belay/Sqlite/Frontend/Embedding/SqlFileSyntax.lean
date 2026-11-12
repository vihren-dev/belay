import Belay.Sqlite.Frontend.Embedding.SqlFileForms

set_option doc.verso true

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
def fileOptions (options : Array Syntax) : TermElabM (Option Syntax × Option Syntax) := do
  let mut section_ := none
  let mut against := none
  for option in options do
    let setting := option[1]
    if setting.getKind == ``sqlFileSection then
      if section_.isSome then throwErrorAt option "the section is given twice; remove one (section := ...) option"
      section_ := some setting[2]
    else
      if against.isSome then throwErrorAt option "the database is given twice; remove one (against := ...) option"
      against := some setting[2]
  return (section_, against)

end Belay.Sqlite
