import Belay.Sqlite.Model.Shared.Resolved.ResolveState
import Belay.Sqlite.Model.Queries.Preparation.WriteStages
import Belay.Sqlite.Model.Queries.Preparation.NameTraceConstraints

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The state after a statement that is not transaction control
({name}`ResolveState.withCatalog`) with the trace of the resolution. -/
def ResolveState.withCatalogTraced (state : ResolveState) (result : TracedResolution) :
    Traced NodeRestriction (Resolved.Statement × ResolveState) :=
  ⟨state.withCatalog result.drop, result.trace⟩

end Belay.Sqlite.Model
