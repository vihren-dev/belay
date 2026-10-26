import Belay.Sqlite.Model.Resolution.ResolveState
import Belay.Sqlite.Model.Resolution.WriteStages
import Belay.Sqlite.Model.Resolution.NameTraceConstraints

set_option doc.verso true

/-! The steps from a resolution of a statement to the next state of a script, with the name trace.
The trace of the statement is the trace of its resolution: the step after the resolution (the
foreign keys and the trigger programs of {lit}`ResolveState.withWrite`) decides no name of the
statement. -/

namespace Belay.Sqlite.Model

/-- The state after a statement that is not transaction control
({name}`ResolveState.withCatalog`) with the trace of the resolution. -/
def ResolveState.withCatalogTraced (state : ResolveState) (result : TracedResolution) :
    Traced NodeRestriction (Resolved.Statement × ResolveState) :=
  ⟨state.withCatalog result.drop, result.trace⟩

/-- The state after a write ({name}`ResolveState.withWrite`) with the trace of the resolution of the
write. A prepare error of the keys or of a trigger program keeps the trace: the write resolved before
it. -/
def ResolveState.withWriteTraced (context : ResolveContext) (state : ResolveState) (result : TracedResolution) :
    Traced NodeRestriction (Resolved.Statement × ResolveState) :=
  ⟨state.withWrite context result.drop, result.trace⟩

end Belay.Sqlite.Model
