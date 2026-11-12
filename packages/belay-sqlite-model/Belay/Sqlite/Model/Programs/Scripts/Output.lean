import Belay.Sqlite.Model.Programs.Scripts.PossibleOutput
import Belay.Sqlite.Model.Shared.Execution.Output

set_option doc.verso true

/-! What one statement of a run gives (ADR 0017, D3): its rows, its number of changes, its
error code, every result that SQLite may give for it, or the reason why the model does not
describe it. The run of {lit}`ScriptRun.lean` gives one output for each
statement that it runs. -/

namespace Belay.Sqlite.Model

/-- The output of a statement from its transition, from its run ({name}`StatementRun`) and from
what the model computes for it with the values bound to its parameters
({name}`statementOutput`, {name}`possibleOutput`):

* a statement that stops with an error gives {name}`Output.error` of its primary result code,
  except {lean}`ExecutionError.unmodeled`, which gives {name}`Output.unmodeled`;
* a query that succeeds gives {name}`Output.ofResults` of its possible results;
* a write with {lit}`RETURNING` that succeeds gives its rows in normal form, because SQLite
  promises no order for them;
* every other statement that succeeds gives {name}`Output.done` of its number of changes, 0
  when it has none;
* a statement for which the model gives no output gives {name}`Output.unmodeled`.

The optional {lit}`initial` database is the one that the sources of the initial origin of a query read in a
two-state observation; use none otherwise. -/
def Output.ofStep (clock : Int) (parameters : List Value) (statement : Resolved.Statement) (before : SqlState)
    (run : StatementRun) (transition : SqlTransition) (initial : Option Database := none) : Output :=
  match haltError transition with
  | some .unmodeled => .unmodeled unmodeledHere
  | some failure@(.prepare _) | some failure@.transactionAlreadyActive | some failure@.noActiveTransaction
  | some failure@.constraintViolation | some failure@.constraintFail | some failure@.constraintRollback
  | some failure@.integerOverflow | some failure@.datatypeMismatch | some failure@.functionError
  | some failure@.nullColumnDefault | some failure@.nonConstantColumnDefault | some failure@.checkColumnDefault
  | some failure@.referenceColumnDefault =>
    .error failure.primaryCode
  | none => match statement with
    | .query .. => match possibleOutput clock parameters statement before transition initial with
      | some results => .ofResults results
      | none => .unmodeled "the model gives no result for this query"
    | .createTable .. | .createView .. | .createIndex .. | .createTrigger .. | .addColumn .. | .rewrite _ | .dropColumn .. | .drop .. | .begin | .commit
    | .rollback | .insert .. | .upsert .. | .insertSelect .. | .update .. | .delete .. | .prepareError _ | .setting .. =>
      match statementOutput clock parameters statement before run transition with
      | some output =>
        if statement.returnsRows then .rows (Resolved.normalForm output.rows) else .done (output.changes.getD 0)
      | none => .unmodeled "the model gives no output for this statement"

end Belay.Sqlite.Model
