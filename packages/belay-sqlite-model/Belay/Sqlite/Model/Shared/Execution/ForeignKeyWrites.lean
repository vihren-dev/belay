import Belay.Sqlite.Model.Shared.Execution.ForeignKeyPhases

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- What a write that runs row by row gives: its effect, the rows that it wrote
({name}`KeyState.written`), what it does to the counters of the connection, and whether the model
describes it on the database. -/
structure KeyRun where
  /-- The effect of the write. -/
  effect : Effect
  /-- The rows that the statement wrote, for its {lit}`RETURNING` rows. -/
  written : List Row
  /-- What the write does to the counters of the connection ({name}`Counts`). -/
  counts : Counts := {}
  /-- Whether the model describes the write: its rows are described ({name}`KeyStop.undescribed`
  does not occur), no subquery reads a table while an action or a trigger changes the tables,
  every table that an action or a trigger changed satisfies its constraints before the write,
  and every changed table has bounded rowids. -/
  ready : Bool

end Belay.Sqlite.Model
