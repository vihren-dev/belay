import Belay.Sqlite.Model.Queries.Fixtures.Examples
import Belay.Sqlite.Model.Shared.Execution.SqlExecution

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.CheckExamples

open Belay.Sqlite.Model Syntax

/-- An unqualified column. -/
def ref (name : Identifier) : Expr := .identifier name .none

#guard (PrepareError.expression (.unknownForeignKeyColumn (name! "zz"))).message ==
  "unknown column \"zz\" in foreign key definition"

end Belay.Sqlite.Model.Resolution.CheckExamples
