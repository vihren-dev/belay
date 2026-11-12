import Belay.Sqlite.Model
import Belay.Sqlite.Schema.Dispatch.Run

set_option doc.verso true

namespace Belay.Sqlite
open Model

/-- Whether a statement of a script is sheltered from a position when it resolves from the given state of
resolution: every successful resolution of it is a resolved statement that is sheltered
({name}`Resolved.Statement.ShelteredFrom`). A statement that resolution refuses is sheltered, because its
step stops the run without a change. -/
def Model.Syntax.Statement.ShelteredAt (position : Nat) (state : ResolveState) (statement : Syntax.Statement) : Prop :=
  ∀ resolved after, resolveStatement runContext state statement = .ok (resolved, after) →
    resolved.ShelteredFrom position

end Belay.Sqlite
