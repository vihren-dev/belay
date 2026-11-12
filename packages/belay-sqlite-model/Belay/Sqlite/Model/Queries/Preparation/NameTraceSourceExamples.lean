import Belay.Sqlite.Model.Queries.Select.MergedNameExamples
import Belay.Sqlite.Model.Queries.Select.SourceListFromArms

set_option doc.verso true

namespace Belay.Sqlite.Model.NameTraceSourceExamples

/-- Whether a result is a source of the given kind and index. -/
def isSource (kind : SourceKind) (index : Nat) : NameResult → Bool
  | .source reference => reference.kind == kind && reference.index == index
  | .found _ | .ambiguous _ | .missing .. | .schema _ | .resultColumn _ | .declares | .compared ..
  | .unreached _ => false

/-- Whether a result is a name that is bound to exactly the given number of columns. -/
def foundCount (count : Nat) : NameResult → Bool
  | .found bindings => bindings.length == count
  | .ambiguous _ | .missing .. | .source _ | .schema _ | .resultColumn _ | .declares | .compared ..
  | .unreached _ => false

/-- Whether a result is a missing name whose candidates are the given number of catalog objects. -/
def missingObjects (count : Nat) : NameResult → Bool
  | .missing .error candidates => candidates.length == count && candidates.all fun
    | .catalogObject .. => true
    | .column _ | .resultAlias .. | .source _ => false
  | .missing .textLiteral _ | .missing .booleanKeyword _ | .missing .rowidName _ | .found _ | .ambiguous _
  | .source _ | .schema _ | .resultColumn _ | .declares | .compared .. | .unreached _ => false

end Belay.Sqlite.Model.NameTraceSourceExamples
