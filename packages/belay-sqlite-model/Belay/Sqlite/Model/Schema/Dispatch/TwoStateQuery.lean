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

/-- For any SELECT, two states with the same catalog resolve it to the same statement or the
same restriction. Proof sketch: {name}`resolveStatement_select` uses only the catalog. -/
theorem select_resolution_of_same_catalog
    (ctx : ResolveContext) (stmt : Syntax.Statement)
    (sel : stmt.asQuery?.isSome = true) (a b : ResolveState)
    (same : a.catalog = b.catalog) :
    (resolveStatement ctx a stmt).map Prod.fst =
      (resolveStatement ctx b stmt).map Prod.fst := by
  cases stmt <;> try contradiction
  simp only [resolveStatement_select, ResolveState.withCatalog, same]
  cases resolveSelect ctx b.catalog _ _ <;> rfl

end Belay.Sqlite.Model
