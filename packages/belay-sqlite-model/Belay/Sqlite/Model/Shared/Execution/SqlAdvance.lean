import Belay.Sqlite.Model.Shared.Execution.SqlCounted
import Belay.Sqlite.Model.Shared.Execution.StatementRun

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- One statement at its supplied zero-based position with its effect. BEGIN records a
snapshot; COMMIT clears it; ROLLBACK restores it. Repeated BEGIN or transaction
closure without a snapshot halts with an error. Other statements use
the effect, which {lit}`advance` computes at the clock value of the position
({name}`SqlState.clock`); an error retains any open transaction, except a ROLLBACK failure,
which rolls it back ({name}`SqlState.failed`). -/
def advanceWith (position : Nat) (statement : Resolved.Statement) (state : SqlState) (effect : Effect) :
    SqlTransition :=
  match statement with
  | .begin => match state.snapshot with
    | some _ => .halt (state.finish (.failure position .transactionAlreadyActive state.database))
    | none => .next { state with snapshot := some state.database }
  | .commit => match state.snapshot with
    | none => .halt (.failure position .noActiveTransaction state.database)
    | some _ => .next { state with snapshot := none }
  | .rollback => match state.snapshot with
    | none => .halt (.failure position .noActiveTransaction state.database)
    | some original => .next { state with database := original, snapshot := none }
  | .createTable .. | .createView .. | .createIndex .. | .createTrigger .. | .addColumn .. | .rewrite _ | .dropColumn .. | .drop .. | .insert .. | .upsert .. | .insertSelect .. | .update ..
  | .delete ..
  | .prepareError _ | .query .. | .setting .. =>
    state.publish position effect

/-- The transition of a statement after its run ({name}`StatementRun`): {name}`advanceWith` of
its effect, with its counts for the counters ({name}`SqlTransition.counted`). -/
def advanceRun (position : Nat) (statement : Resolved.Statement) (state : SqlState) (run : StatementRun) :
    SqlTransition :=
  (advanceWith position statement state run.effect).counted run.counts

/-- The statements of a script with the values bound to each: statement {lit}`i` (from 0) gets
item {lit}`i` of {lit}`values`, or the empty list when {lit}`values` has no such item. For
example, {lean}`bindValues [1, 2] [[.integer 5]] = [(1, [.integer 5]), (2, [])]`. Use
{lean}`([] : List (List Value))` as {lit}`values` for a script that binds no values. -/
def bindValues {α : Type} : List α → List (List Value) → List (α × List Value)
  | [], _ => []
  | statement :: rest, values => (statement, values.headD []) :: bindValues rest values.tail

/-- For every statement, rest of the script, list of values and rest of the lists,
{name}`bindValues` of the script and the lists is the pair of the first statement and the first
list, followed by {name}`bindValues` of the rest of the script and the rest of the lists. Proof
sketch: the definition. -/
@[simp] theorem bindValues_cons_cons {α : Type} (statement : α) (rest : List α) (values : List Value)
    (later : List (List Value)) :
    bindValues (statement :: rest) (values :: later) = (statement, values) :: bindValues rest later := rfl

/-- For every script and list of lists of values, the statements of {name}`bindValues` are the
script. Proof sketch: induction on the script. -/
@[simp] theorem map_fst_bindValues {α : Type} (script : List α) (values : List (List Value)) :
    (bindValues script values).map (·.1) = script := by
  induction script generalizing values with
  | nil => rfl
  | cons statement rest ih => simp [bindValues, ih]

end Belay.Sqlite.Model
