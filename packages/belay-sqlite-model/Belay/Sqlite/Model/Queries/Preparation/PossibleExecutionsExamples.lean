import Belay.Sqlite.Model.Queries.Preparation.CounterReadExamples
import Belay.Sqlite.Model.Queries.Preparation.ForeignKeyExamples
import Belay.Sqlite.Model.Shared.Resolved.Context

set_option doc.verso true

namespace Belay.Sqlite.Model.PossibleExecutionsExamples

open Belay.Sqlite.Model Resolution.Examples

/-- The context of the examples: the default profile, in execution mode. -/
def context : ResolveContext := { profile := defaults, mode := .execution }

end Belay.Sqlite.Model.PossibleExecutionsExamples
