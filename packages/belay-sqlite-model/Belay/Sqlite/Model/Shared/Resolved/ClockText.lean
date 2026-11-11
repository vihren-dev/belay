import Belay.Sqlite.Model.Shared.Values.Declarations

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The three time keywords. -/
inductive TimeKeyword where
  /-- {lit}`CURRENT_TIME`: {lit}`HH:MM:SS`. -/
  | time
  /-- {lit}`CURRENT_DATE`: {lit}`YYYY-MM-DD`. -/
  | date
  /-- {lit}`CURRENT_TIMESTAMP`: {lit}`YYYY-MM-DD HH:MM:SS`. -/
  | timestamp
  deriving Repr, DecidableEq

end Belay.Sqlite.Model
