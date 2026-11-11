import Belay.Sqlite.Model.Shared.Execution.SqlExecution
import Belay.Sqlite.Model.Queries.Fixtures.Examples
import Belay.Sqlite.Model.Queries.Evaluation.Functions

set_option doc.verso true

namespace Belay.Sqlite.Model.ClockExamples
open Belay.Sqlite.Model

-- Each time keyword is its date and time function without arguments.
example (clock : Int) : TimeKeyword.timestamp.value clock = Resolved.DateFunction.datetime.value clock [] := rfl

end Belay.Sqlite.Model.ClockExamples
