import Belay.Sqlite.Model.Queries.Preparation.TwoStateStatementLaws
import Belay.Sqlite.Model.Queries.Preparation.SyntaxSchema
import Belay.Sqlite.Model.Queries.Select.SelectResolution

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Whether the query or one of its subqueries, which hold every derived table, expression subquery, common
table and compound term of the statement, has a source with a schema name. Only such a query needs the
initial database. A schema name in a column, as in {lit}`before.t.a`, needs a source with that schema name,
so it does not change the result. -/
def usesSchema (query : Syntax.Subquery) (subqueries : List Syntax.Subquery) : Bool :=
  (query :: subqueries).any Syntax.Subquery.hasSchemaSource

/-- Resolve a query against the catalog of the initial database and the catalog of the current database.
A query with no source that has a schema name resolves as {name}`resolveSelect` does without an initial
catalog, so that the initial catalog cannot change it ({lit}`resolveTwoState_ordinary`); a query with such a
source resolves its sources of {lit}`before` in the initial catalog and all others in the current catalog.
A schema name other than {lit}`before` is the restriction {name}`RestrictionKind.initialDatabase`. -/
def resolveTwoState (context : ResolveContext) (initial current : Catalog) (query : Syntax.Subquery)
    (subqueries : List Syntax.Subquery) : StatementResolution :=
  if usesSchema query subqueries then resolveSelect context current query subqueries (some initial)
  else resolveSelect context current query subqueries

/-- For every context, catalogs, query and subqueries such that neither the query nor a subquery has a source
with a schema name, {name}`resolveTwoState` is {name}`resolveSelect` without an initial catalog, whatever the
initial catalog is. In plain words: if no source names a schema, the initial catalog is not used. Proof sketch:
the premise selects the ordinary branch of {name}`resolveTwoState`, and the branch is the right side. -/
theorem resolveTwoState_ordinary (context : ResolveContext) (initial current : Catalog) (query : Syntax.Subquery)
    (subqueries : List Syntax.Subquery) (plain : usesSchema query subqueries = false) :
    resolveTwoState context initial current query subqueries = resolveSelect context current query subqueries := by
  simp [resolveTwoState, plain]

end Belay.Sqlite.Model
