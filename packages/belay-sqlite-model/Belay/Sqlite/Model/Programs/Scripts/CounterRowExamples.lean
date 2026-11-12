import Belay.Sqlite.Model.Programs.StatementRunLaws.CounterExamples
import Belay.Sqlite.Model.Programs.Clock.TriggerRunExamples
import Belay.Sqlite.Model.Schema.Writes.CounterRowExamples

set_option doc.verso true

namespace Belay.Sqlite.Model.CounterRowExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- The counters after the statements, from the empty database on a new connection, under the
profile. -/
def countersUnder (profile : Profile) (script : List Syntax.Statement) : Counters :=
  (runScriptFrom { profile, mode := .execution } none 0 { state := { database := {}, counters := Counters.newConnection } }
    (bindValues script [])).connection.state.counters

/-- The state after the resolved statements from the state, where a statement that halts leaves its
counts on the counters, as {name}`Connection.afterError` does. The kernel cannot reduce the support
check of every statement ({name}`runScriptFrom` makes it), so these examples run the transitions
({name}`advance`) without it. -/
def stateAfter (position : Nat) : List (Resolved.Statement × List Value) → SqlState → SqlState
  | [], state => state
  | (statement, parameters) :: rest, state => match advance position statement parameters state with
    | .next next => stateAfter (position + 1) rest next
    | .halt _ => { state with counters := state.counters.apply (state.statementRun (state.clock position) parameters statement).counts }

/-- The counters after the statements, from the empty database on a new connection, under the
profile, without the support check of {name}`stateAfter`. -/
def countersOfRun (profile : Profile) (script : List Syntax.Statement) : Counters :=
  (stateAfter 0 (bindValues (statements (migration [] script profile)) [])
    { database := {}, counters := Counters.newConnection }).counters

/-- An {lit}`INSERT OR REPLACE` that replaces a row whose child cascades: the statement changes the
one row that it inserted, the replaced row does not count, the cascade adds one to the total, and the
last rowid is the rowid 3 of the new row. -/
example : countersOfRun ForeignKeyExamples.keysOn (ForeignKeyExamples.schema .cascade .noAction ++
    [.insert (name! "p") none [[.numeric "1"]] [] (some .replace)]) =
    { changes := some 1, totalChanges := some 5, lastInsertRowid := some 3 } := by decide +kernel

/-- An INSERT of two rows checks the keys at its end, after it stored both rows, so the last rowid
is the rowid 3 of the second row also when the first row has no parent. -/
example : countersOfRun ForeignKeyExamples.keysOn (plainSchema ++ [insertChildren ["9", "2"]]) =
    { changes := some 0, totalChanges := some 3, lastInsertRowid := some 3 } := by decide +kernel

end Belay.Sqlite.Model.CounterRowExamples
