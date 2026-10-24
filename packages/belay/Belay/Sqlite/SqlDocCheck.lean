import Belay.Sqlite.SqlDocObservation
import Belay.Sqlite.ProgramRun

set_option doc.verso true

namespace Belay.Sqlite.SqlDoc

/-- Check the actual outputs of a script started from the supplied database and environment.
Each invocation starts a fresh connection and statement index. The existing {name}`Database.run`
supplies all execution semantics, including bindings, clocks, counters and alternatives.
Use {name}`Env.default` when the SQL does not need an explicit clock or initial counter. -/
def check (database : Database) (environment : Env) (script : Script)
    (expectation : Expectation) : Except Failure Unit :=
  checkOutputs expectation (database.run script environment).outputs

end Belay.Sqlite.SqlDoc
