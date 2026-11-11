import Belay.Sqlite.Model.Schema.Dispatch.Execution
import Belay.Sqlite.Model.Queries.Preparation.InitialSourceExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.TwoStateFixtures

open Resolved

/-- The source rows of a query of one source over the current database and the optional initial database. -/
def rowsOf (source : Source) (initial : Option Database) : Option (List (List Value)) :=
  ((readsFrom source).source (statementContext 0 {} [] currentT [] initial) currentT initial).map (·.rows)

/-- An initial source without an initial database, or at a position that the initial database lacks,
gives no rows, and never the rows of the current table. -/
example : rowsOf (.initialTable 1) none = none := by decide +kernel

end Belay.Sqlite.Model.TwoStateFixtures
