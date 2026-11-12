import Belay.Sqlite.Model.Shared.Execution.SqlExecution
import Belay.Sqlite.Model.Queries.Fixtures.Examples

set_option doc.verso true

namespace Belay.Sqlite.Model.TriggerExamples

open Belay.Sqlite.Model

#guard (PrepareError.triggerExists (name! "r")).message == "trigger r already exists"
#guard (PrepareError.expression .triggerOnSystemTable).message == "cannot create trigger on system table"

#guard (PrepareError.noSuchTrigger (name! "r")).message == "no such trigger: r"

#guard (PrepareError.expression .raiseOutsideTrigger).message == "RAISE() may only be used within a trigger-program"

end Belay.Sqlite.Model.TriggerExamples
