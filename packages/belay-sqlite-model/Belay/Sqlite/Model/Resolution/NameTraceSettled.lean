import Belay.Sqlite.Model.Resolution.NameTraceTypes

set_option doc.verso true

/-! The final form of a trace. The resolver can decide a name twice: it resolves the sources of
{lit}`FROM` again when the derived tables of a query have their columns, and the second decision
has the columns of the derived tables. The trace of a statement holds each name once, where the
resolver first reached it, with the last decision. -/

namespace Belay.Sqlite.Model

/-- The form of the comparison that a result records, or none for any other result. A
{lit}`BETWEEN` records two comparisons at one path, the lower and the upper bound. -/
def NameResult.comparisonForm : NameResult → Option ComparisonForm
  | .compared form _ _ => some form
  | .found _ | .ambiguous _ | .missing .. | .source _ | .schema _ | .resultColumn _ | .declares
  | .unreached _ => none

/-- Whether two occurrences are one name of the statement: they have the same path, the same role,
the same exactness and, for a comparison, the same form. -/
def NameOccurrence.sameNode (first second : NameOccurrence) : Bool :=
  first.path == second.path && first.role == second.role && first.exact == second.exact &&
    first.result.comparisonForm == second.result.comparisonForm

/-- The trace with each name once: an occurrence stays at the place of the first occurrence of its
node ({name}`NameOccurrence.sameNode`), and holds what the last occurrence of that node decided. -/
def NameTrace.settled (trace : NameTrace) : NameTrace :=
  trace.zipIdx.filterMap fun (occurrence, position) =>
    if (trace.take position).any (·.sameNode occurrence) then none
    else some ((trace.reverse.find? (·.sameNode occurrence)).getD occurrence)

end Belay.Sqlite.Model
