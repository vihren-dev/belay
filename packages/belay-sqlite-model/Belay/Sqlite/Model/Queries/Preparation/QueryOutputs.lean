import Belay.Sqlite.Model.Shared.Execution.Output

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Whether the statement only reads: a {lit}`SELECT`, or a pragma that only reads
({name}`Syntax.Pragma.readsOnly`). -/
def Syntax.Statement.readsOnly : Syntax.Statement → Bool
  | .select .. => true
  | .pragma form => form.readsOnly
  | .createTable .. | .createView .. | .createIndex .. | .addColumn .. | .renameTable .. | .renameColumn .. | .dropColumn .. | .dropTable .. | .dropView ..
  | .dropIndex .. | .begin | .commit | .rollback | .insert .. | .insertSelect .. | .update .. | .delete ..
  | .createTrigger .. | .dropTrigger .. => false

end Belay.Sqlite.Model
