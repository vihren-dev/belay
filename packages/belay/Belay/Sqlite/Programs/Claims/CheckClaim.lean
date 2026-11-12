import Lean.Meta.ForEachExpr
import Belay.Sqlite.Programs.Reasoning.ExecutionViewEquivalence
import Belay.Sqlite.Programs.Claims.Queries
import Belay.Sqlite.Frontend.Embedding.SqlSource

set_option doc.verso true

namespace Belay.Sqlite.Check

open Lean Meta

/-- Query predicates whose first two arguments give the script and observed database. -/
def directQueryNames : Array Name :=
  #[``Holds, ``Empty, ``Fails]

end Belay.Sqlite.Check
