import Belay.Sqlite.Model.Queries.Preparation.ResolveStatementApplied
import Belay.Sqlite.Model.Queries.Preparation.AdmittedAtomsSchemaExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.AdmittedRunsConditionExamples

open Belay.Sqlite.Model Resolution.Examples

/-- The context of a script that runs, with the default profile. -/
def execution : ResolveContext := { profile := defaults, mode := .execution }

end Belay.Sqlite.Model.AdmittedRunsConditionExamples
