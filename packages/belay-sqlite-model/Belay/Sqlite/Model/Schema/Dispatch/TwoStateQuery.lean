import Belay.Sqlite.Model.Schema.Ddl.StatementArms
import Belay.Sqlite.Model.Schema.Dispatch.StatementArms
import Belay.Sqlite.Model.Schema.Dispatch.TwoStateStatementLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The query and the list of subqueries of a {lit}`SELECT` statement, as
{name}`resolveStatement` gives them to the resolver; none for every other statement. -/
def Syntax.Statement.asQuery? : Syntax.Statement → Option (Syntax.Subquery × List Syntax.Subquery)
  | .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound =>
    some ({ columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none, having, distinct, compound },
      subqueries)
  | .createView .. | .createTable .. | .createIndex .. | .addColumn .. | .renameTable .. | .renameColumn .. | .dropColumn .. | .dropTable .. | .dropView ..
  | .dropIndex .. | .begin | .commit | .rollback | .insert .. | .insertSelect .. | .update .. | .delete .. | .pragma ..
  | .createTrigger .. | .dropTrigger .. => none

end Belay.Sqlite.Model
