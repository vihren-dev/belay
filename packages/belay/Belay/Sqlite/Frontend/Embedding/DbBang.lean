import Belay.Sqlite.Frontend.Embedding.SqlTerm
import Belay.Sqlite.Frontend.Embedding.SqlEditorInfo

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term Meta

/-- {lit}`db! "SQL"`: the database that the statements of the SQL text build on the empty
database, as {lit}`(Database.Raw.run {} (sql "SQL")).connection.state.database` gives it. For
example, {lit}`db! r"CREATE TABLE t(a); INSERT INTO t VALUES (1)"` is a database with the table
{lit}`t` and one row. Use {lit}`Database.empty` for a database without tables. -/
syntax (name := dbBangTerm) "db! " str : term

/-- The error of a parameter in the text of {lit}`db!`: the database literal has no arguments, so
the parameter has no value. -/
def parameterDiagnostic (parameter : Translation.Parameter) : Diagnostic :=
  { start := parameter.start, stop := parameter.stop,
    message := s!"the parameter {parameter.text} has no value, because db! has no arguments; " ++
      "write the value in the SQL text in place of the parameter" }

end Belay.Sqlite
