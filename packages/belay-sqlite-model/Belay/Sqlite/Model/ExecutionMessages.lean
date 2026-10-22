import Belay.Sqlite.Model.Output
import Belay.Sqlite.Model.Resolution.Messages

set_option doc.verso true

/-! The message of a statement that fails while it runs, as an elaboration error shows it. Where
the model keeps what SQLite's message says, the text is SQLite 3.51's, measured with the
{lit}`sqlite3` shell. A constraint failure and a failed function have no such text, because the
errors of the model do not keep the constraint or SQLite's message. -/

namespace Belay.Sqlite.Model

/-- The message for a constraint failure under ABORT, FAIL or ROLLBACK. It starts with SQLite's
text for the result code {lit}`SQLITE_CONSTRAINT` ({lit}`sqlite3_errstr`). SQLite's message for
the statement also names the constraint, for example
{lit}`NOT NULL constraint failed: invoices.customer`; the errors of the model do not keep the
constraint, so this text says that it does not name it, and tells the user where to see
SQLite's message. This is the only place that gives the text. -/
def constraintFailedMessage : String :=
  "constraint failed; the model does not name the constraint that fails. Run the statement in " ++
    "the sqlite3 shell to see SQLite's message"

/-- The message for a function that fails while the statement runs, such as a JSON function
with malformed JSON. -/
def functionFailedMessage : String :=
  "a function of the statement failed, for example on malformed JSON; the model does not keep " ++
    "SQLite's message for it. Run the statement in the sqlite3 shell to see that message"

/-- The message of the error of the statement, as SQLite 3.51 gives it where the model keeps
what the message says:

* {name}`ExecutionError.prepare` gives SQLite's message of the prepare error
  ({name}`PrepareError.message`);
* {name}`ExecutionError.noActiveTransaction` gives SQLite's text for ROLLBACK, and for every
  other statement its text for COMMIT and END;
* a constraint failure gives {name}`constraintFailedMessage`, which says that the model does
  not name the constraint;
* {name}`ExecutionError.functionError` gives {name}`functionFailedMessage`, which is not
  SQLite's;
* {name}`ExecutionError.unmodeled` gives {name}`unmodeledHere`; a run ends at such a statement,
  so a failure of a run does not have it.

For example, {assert}`ExecutionError.integerOverflow.message .commit = "integer overflow"`. -/
def ExecutionError.message (statement : Resolved.Statement) : ExecutionError → String
  | .unmodeled => unmodeledHere
  | .prepare error => error.message
  | .transactionAlreadyActive => "cannot start a transaction within a transaction"
  | .noActiveTransaction => match statement with
    | .rollback => "cannot rollback - no transaction is active"
    | .createTable .. | .createIndex .. | .createTrigger .. | .addColumn .. | .drop .. | .begin | .commit
    | .insert .. | .upsert .. | .update .. | .delete .. | .prepareError _ | .query .. | .setting _ =>
      "cannot commit - no transaction is active"
  | .constraintViolation | .constraintFail | .constraintRollback => constraintFailedMessage
  | .integerOverflow => "integer overflow"
  | .datatypeMismatch => "datatype mismatch"
  | .functionError => functionFailedMessage
  | .nullColumnDefault => "Cannot add a NOT NULL column with default value NULL"
  | .nonConstantColumnDefault => "Cannot add a column with non-constant default"
  | .checkColumnDefault => "CHECK constraint failed"

end Belay.Sqlite.Model
