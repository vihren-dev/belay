import Belay.Sqlite.Model.Resolution.Context
import Belay.Sqlite.Model.Resolution.CatalogDrop
import Belay.Sqlite.Model.Resolution.SyntaxParameters
import Belay.Sqlite.Model.Resolution.SyntaxSchema

set_option doc.verso true

/-! CREATE VIEW retains unresolved syntax. SQLite checks parameters and the object
name now; referenced objects and output-column counts are checked when the view is used. -/

namespace Belay.Sqlite.Model

/-- Resolve CREATE VIEW: parameters anywhere in the stored body are a SQLite error, and a source
with a schema name in the body, as {lit}`before.t` has, is the restriction
{name}`RestrictionKind.initialDatabase` because SQLite refuses it; then reserved names and existing objects are checked. IF NOT EXISTS keeps an existing
table or view, but an index with the name remains an error. A fresh name appends the
unresolved definition; missing references and cycles do not prevent creation. -/
def resolveCreateView (catalog : Catalog) (name : Identifier) (ifNotExists : Bool)
    (view : CatalogView) : StatementResolution :=
  if view.query.hasParameter || view.subqueries.any Syntax.Subquery.hasParameter then
    prepareError catalog .viewVariables
  else if view.query.hasSchemaSource || view.subqueries.any Syntax.Subquery.hasSchemaSource then
    restrict [] .initialDatabase
  else if reservedName name then prepareError catalog (.expression (.reservedName name))
  else match catalog.find name with
  | some (_, { entry := .table _, .. }) =>
    if ifNotExists then .ok (.drop [], catalog.drop []) else prepareError catalog (.tableExists name)
  | some (_, { entry := .view _, .. }) =>
    if ifNotExists then .ok (.drop [], catalog.drop []) else prepareError catalog (.viewExists name)
  | some (_, { entry := .index _, .. }) => prepareError catalog (.indexNameUsed name)
  | some (_, { entry := .trigger _, .. }) => prepareError catalog (.tableExists name)
  | none => .ok (.createView catalog.length name view, catalog.createView name view)

end Belay.Sqlite.Model
