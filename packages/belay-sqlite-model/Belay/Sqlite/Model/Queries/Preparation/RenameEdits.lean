import Belay.Sqlite.Model.Queries.Preparation.NameTraceTypes
import Belay.Sqlite.Model.Shared.Resolved.Restrictions

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Whether the source is the table at the position itself, not a view or a derived table that reads it. -/
def SourceRef.namesTable (source : SourceRef) (position : Nat) : Bool :=
  source.kind == .baseTable && source.position == some position

/-- Whether the binding is the column at the index of the table at the position. The columns of
{lit}`NEW` and {lit}`OLD` are those of the table of the trigger; {lit}`triggerOn` tells whether that is the
table at the position. -/
def Binding.isColumnOf (binding : Binding) (position index : Nat) (triggerOn : Bool) : Bool :=
  binding.column.index == index && match binding.source.kind with
    | .baseTable => binding.source.position == some position
    | .triggerRow => triggerOn
    | .initialTable | .storedView | .commonTable | .derivedTable | .tableFunction | .proposedRow => false

end Belay.Sqlite.Model
