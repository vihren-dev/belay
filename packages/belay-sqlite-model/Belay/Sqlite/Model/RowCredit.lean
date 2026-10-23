import Belay.Sqlite.Model.TriggerRun

set_option doc.verso true

/-! The rows of the nested writes of a statement (ADR 0024, D2, checked natively with 3.51.0):
a program of a trigger and an action of a foreign key write through nested writes. SQLite adds
the rows of a nested write to {lit}`total_changes()` when the nested write completes, also when
the statement fails later, and loses the rows of a nested write that fails. The rows of the
nested write never count for {lit}`changes()`, and its inserts do not set
{lit}`last_insert_rowid()`. -/

namespace Belay.Sqlite.Model

/-- The nested run with the counts of ADR 0024, D2: the write runs with no row counted. When it
completes, its rows move to the credited rows of the state. When it fails, its rows are lost, and
the credited rows of the nested writes that completed before stay in the stop. In every case the
rows counted and the last inserted row are those from before the write, because the rows of a
nested write are not the rows of the statement. -/
def NestedRun.credited (nested : NestedRun) : NestedRun := fun frame work state =>
  let restore (reached : KeyState) : KeyState := { reached with own := state.own, inserted := state.inserted }
  match nested frame work { state with own := 0 } with
  | .ok reached => .ok { restore reached with credited := reached.credited + reached.own }
  | .error (.error reason reached) => .error (.error reason (restore reached))
  | .error (.stopped algorithm reached) => .error (.stopped algorithm (restore reached))
  | .error .undescribed => .error .undescribed

end Belay.Sqlite.Model
