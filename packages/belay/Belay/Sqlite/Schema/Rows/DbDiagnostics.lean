import Belay.Sqlite.Schema.Dispatch.SqlDiagnostics
import Belay.Sqlite.Model

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- What the user can do after the error of the statement, appended to SQLite's message. A
failed {lit}`CREATE UNIQUE INDEX` writes no row, so its text names the rows of the table and the
index. The texts of a function failure, and of a constraint failure in a write that can fire a
trigger or that checks foreign keys ({name}`triggerOrKeyConstraintMessage`), say it already. -/
def failureAction (statement : Resolved.Statement) : ExecutionError → String
  | .transactionAlreadyActive | .noActiveTransaction =>
    "; remove the statement, or add the BEGIN or COMMIT that it needs"
  | .integerOverflow | .datatypeMismatch | .nullColumnDefault | .nonConstantColumnDefault
  | .checkColumnDefault | .referenceColumnDefault | .unmodeled | .prepare _ =>
    "; correct the statement, or the statements before it that give the data that it reads"
  | .constraintViolation | .constraintFail | .constraintRollback => match statement with
    | .createIndex .. => "; remove the rows whose values of the index are equal, or change the index"
    | .insert .. | .upsert .. | .insertSelect .. | .update .. | .delete .. | .drop .. | .createTable .. | .createView .. | .createTrigger ..
    | .addColumn .. | .begin | .commit | .rollback | .prepareError _ | .query .. | .setting .. | .rewrite _ | .dropColumn .. =>
      match statement.writeRules with
      | some _ => ""
      | none => "; correct the row, or the statement that writes it"
  | .functionError => ""

end Belay.Sqlite
