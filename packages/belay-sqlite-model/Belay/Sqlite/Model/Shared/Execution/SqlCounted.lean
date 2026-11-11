import Belay.Sqlite.Model.Shared.Execution.SqlState

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The transition of a statement with the counts it gives the counters: a transition that
continues takes the counters after the counts ({name}`Counters.apply`); a halt stays. -/
def SqlTransition.counted (counts : Counts) : SqlTransition → SqlTransition
  | .next state => .next { state with counters := state.counters.apply counts }
  | .halt outcome => .halt outcome

end Belay.Sqlite.Model
