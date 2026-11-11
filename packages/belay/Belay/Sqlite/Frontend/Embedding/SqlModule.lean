import Belay.Sqlite.Frontend.Embedding.SqlFileSyntax

set_option doc.verso true

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

end Belay.Sqlite
