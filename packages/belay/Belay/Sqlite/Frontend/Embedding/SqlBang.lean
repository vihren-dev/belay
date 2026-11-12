import Belay.Sqlite.Frontend.Embedding.SqlTerm
import Belay.Sqlite.Frontend.Embedding.SqlEditorInfo

set_option doc.verso true

namespace Belay.Sqlite

open Lean Elab Term

/-- {lit}`sql! db "SQL"`: the script of the statements of the SQL text, as {lit}`sql "SQL"`
gives it, after a check of the statements against the database {lit}`db`, which must have a
value while the file elaborates. The term does not use {lit}`db`, so
{lit}`sql! db r"..."` and {lit}`sql r"..."` are equal by {lit}`rfl`. Use {lit}`sql` for a script
that runs on a database that is a variable. -/
syntax:max (name := sqlBangTerm) "sql! " term:max str : term

end Belay.Sqlite
