import Belay.Sqlite.Frontend.Embedding.DbDiagnostics

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- The database at the start of a statement, as far as the editor knows it. For example,
{lean}`({ state := { catalog := [] }, rows? := none } : StatementContext)` knows no table and no rows. -/
structure StatementContext where
  /-- The state of resolution at the start of the statement: its catalog and settings. The
  resolver run that decides the statement starts from it, and the name trace of the statement
  comes from that run. -/
  state : ResolveState
  /-- The stored rows of each catalog position at the start of the statement, or none when an
  earlier statement may have changed them and no run measured them. -/
  rows? : Option (List (List Row))

end Belay.Sqlite
