import Belay.Sqlite.Model.Queries.Fixtures.Examples
import Belay.Sqlite.Model.Shared.Execution.SqlExecution

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.WithoutRowidExamples

open Belay.Sqlite.Model

#guard (PrepareError.expression (.primaryKeyMissing (name! "n"))).message == "PRIMARY KEY missing on table n"

/-- Two untyped columns {lit}`a, b`. -/
def twoColumns : List CatalogColumn := [{ name := name! "a", declaredType := none }, { name := name! "b", declaredType := none }]

end Belay.Sqlite.Model.Resolution.WithoutRowidExamples
