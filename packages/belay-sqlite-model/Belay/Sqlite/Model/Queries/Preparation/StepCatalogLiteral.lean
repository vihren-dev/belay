import Belay.Sqlite.Model.Queries.Preparation.ResolveStateSpec
import Belay.Sqlite.Model.Shared.Execution.SqlState

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- A connection state agrees with a resolution state when the visible database has the
current catalog of the resolution, and an open transaction's snapshot has the saved
catalog: both are absent, or both are present with equal catalogs. -/
def SqlState.Agrees (sql : SqlState) (state : ResolveState) : Prop :=
  sql.database.catalog = state.catalog ∧ sql.snapshot.map (·.catalog) = state.saved

end Belay.Sqlite.Model
