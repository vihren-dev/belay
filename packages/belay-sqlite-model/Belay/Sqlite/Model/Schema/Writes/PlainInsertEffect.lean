import Belay.Sqlite.Model.Schema.Writes.KeysUniqueWrites
import Belay.Sqlite.Model.Shared.Execution.ScriptRun

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every database, target, keys, table, supplied rows and result table: if the write of
the result succeeds, it gives the database with the rows of the result stored at the target.
Proof sketch: split the data-domain check and the checked write; each failing branch is an error,
and the successful branch stores the rows. -/
theorem insertOutcome_ok {database : Model.Database} {target : Nat} {keys : List UniqueKey}
    {table : Table} {rows : List (List Value)} {result : Table} {after : Model.Database}
    (ok : insertOutcome database target keys table rows result = .ok after) :
    after = database.setRows target result.rows := by
  unfold insertOutcome at ok
  split at ok
  · dsimp only at ok
    split at ok <;> cases ok
  · unfold checkedWrite at ok
    split at ok
    · cases ok; rfl
    · cases ok

end Belay.Sqlite.Model
