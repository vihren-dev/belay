import Belay.Sqlite.Model.Shared.Syntax.Syntax

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Whether a statement is BEGIN, COMMIT or ROLLBACK. -/
def Syntax.Statement.transactionControl : Syntax.Statement → Bool
  | .begin | .commit | .rollback => true
  | .createTable .. | .createView .. | .createIndex .. | .addColumn .. | .renameTable .. | .renameColumn .. | .dropColumn .. | .dropTable .. | .dropView .. | .dropIndex .. | .createTrigger ..
  | .dropTrigger .. | .insert .. | .insertSelect .. | .update .. | .delete .. | .select .. | .pragma _ => false

end Belay.Sqlite.Model
