import Belay.Sqlite.Model.Queries.Preparation.StatementSingleton
import Belay.Sqlite.Model.Queries.Preparation.ViewDefinitions
import Belay.Sqlite.Model.Queries.Select.SelectResolution

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every successful resolution of SELECT, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of SELECT. -/
theorem resolveSelect_single (context : ResolveContext) (catalog after : Catalog)
    (query : Syntax.Subquery) (subqueries : List Syntax.Subquery) (statement : Resolved.Statement)
    (ok : resolveSelect context catalog query subqueries = .ok (statement, after)) :
    statement.fromQuery = false := by
  unfold resolveSelect resolveSelectTraced at ok
  dsimp only [Traced.drop] at ok
  simp only [prepareError, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

/-- For every successful resolution of CREATE VIEW, the resolved statement is no INSERT from a query without
rules ({name}`Resolved.Statement.fromQuery`). Proof sketch: every branch of the resolver gives a prepare error
or a statement of the form of CREATE VIEW. -/
theorem resolveCreateView_single (catalog after : Catalog) (name : Identifier)
    (ifNotExists : Bool) (view : CatalogView) (statement : Resolved.Statement)
    (ok : resolveCreateView catalog name ifNotExists view = .ok (statement, after)) :
    statement.fromQuery = false := by
  unfold resolveCreateView at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; rfl)
    | (cases ok)

end Belay.Sqlite.Model
