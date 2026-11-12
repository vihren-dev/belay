import Belay.Sqlite.Model.Shared.Execution.ScriptRun
import Belay.Sqlite.Model.Queries.Fixtures.Examples

set_option doc.verso true

namespace Belay.Sqlite.Model.PragmaSchemaExamples

open Belay.Sqlite.Model Syntax

/-- {lit}`JOIN s USING (schema)`. -/
def usingSchema : Join :=
  { operator := [], source := { table := name! "s", alias := none, arguments := none }, condition := none,
    usingColumns := some [name! "schema"] }

end Belay.Sqlite.Model.PragmaSchemaExamples
