import Belay.Sqlite.Model.Resolution.NameTraceTypes

set_option doc.verso true

/-! Change the sources that a name result mentions. The name trace needs this when a source is
known under another kind after the resolution, for example the use of a stored view. -/

namespace Belay.Sqlite.Model

/-- The binding with the change applied to its source. -/
def Binding.mapSource (change : SourceRef → SourceRef) (binding : Binding) : Binding :=
  { binding with source := change binding.source }

/-- The candidate with the change applied to every source that it mentions. -/
def Candidate.mapSources (change : SourceRef → SourceRef) : Candidate → Candidate
  | .column binding => .column (binding.mapSource change)
  | .source reference => .source (change reference)
  | .resultAlias name index => .resultAlias name index
  | .catalogObject kind name position => .catalogObject kind name position

/-- The result with the change applied to every source that it mentions. -/
def NameResult.mapSources (change : SourceRef → SourceRef) : NameResult → NameResult
  | .found bindings => .found (bindings.map (·.mapSource change))
  | .ambiguous candidates => .ambiguous (candidates.map (·.mapSources change))
  | .missing use candidates => .missing use (candidates.map (·.mapSources change))
  | .source reference => .source (change reference)
  | .schema known => .schema known
  | .resultColumn index => .resultColumn index
  | .declares => .declares
  | .compared form affinity collation => .compared form affinity collation
  | .unreached why => .unreached why

end Belay.Sqlite.Model
