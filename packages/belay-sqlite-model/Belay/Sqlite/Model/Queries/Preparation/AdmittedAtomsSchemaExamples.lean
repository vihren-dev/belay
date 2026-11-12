import Belay.Sqlite.Model.Queries.Fixtures.Examples
import Belay.Sqlite.Model.Queries.Preparation.ResolveStateSpec

set_option doc.verso true

namespace Belay.Sqlite.Model.AdmittedAtomsSchemaExamples

open Belay.Sqlite.Model Resolution.Examples

/-- The context of a script that runs. -/
def execution : ResolveContext := { profile := defaults, mode := .execution }

-- The state at the start of a script is valid when the catalog is: no catalog is saved.
example : (ResolveState.initial defaults []).Valid defaults.limits :=
  ⟨by decide +kernel, by simp [ResolveState.initial]⟩

end Belay.Sqlite.Model.AdmittedAtomsSchemaExamples
