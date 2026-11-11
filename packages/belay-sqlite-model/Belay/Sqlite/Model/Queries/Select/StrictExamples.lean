import Belay.Sqlite.Model.Queries.Fixtures.Examples
import Belay.Sqlite.Model.Shared.Execution.SqlExecution

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.StrictExamples

open Belay.Sqlite.Model Syntax

/-- An unqualified column. -/
def ref (name : Identifier) : Expr := .identifier name .none

end Belay.Sqlite.Model.Resolution.StrictExamples
