import Belay.Sqlite.Model.Queries.Preparation.StepCatalogLiteral
import Belay.Sqlite.Model.Schema.Dispatch.Connection

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every state and resolution state: if the state agrees with the resolution state
({name}`SqlState.Agrees`), the connection with the state and the resolution state's settings
has that resolution state. Proof sketch: the catalogs and the saved catalogs are equal by the
agreement, and the settings are the resolution state's; the structures are then equal field by
field. -/
theorem Connection.resolveState_of_agrees {state : SqlState} {target : ResolveState} (agrees : state.Agrees target) :
    ({ state, foreignKeys := target.foreignKeys, recursiveTriggers := target.recursiveTriggers } : Connection).resolveState = target := by
  obtain ⟨catalog, saved⟩ := agrees
  cases target
  simp_all [Connection.resolveState]

end Belay.Sqlite.Model
