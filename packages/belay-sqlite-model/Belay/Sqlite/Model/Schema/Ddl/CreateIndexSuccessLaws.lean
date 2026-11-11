import Belay.Sqlite.Model.Schema.Ddl.StatementArms
import Belay.Sqlite.Model.Schema.Dispatch.StatementArms
import Belay.Sqlite.Model.Schema.Ddl.DatabaseLookup

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The conditions for CREATE INDEX on this database:

* the catalog finds the named table at some position with some shape;
* neither the table name nor the index name is reserved, and no table or index uses the
  index name ({name}`Catalog.find` ignores triggers);
* the terms and optional filter resolve over that table under the context's DQS setting;
* if the new index is unique, its resolved key has no conflicting pair among that table's
  rows ({name}`LiteralData.uniqueRows`). A nonunique index imposes no row condition.

Use these conditions for a success claim when SQL cannot inspect the index name. -/
def CreateIndexConditions (context : ResolveContext) (database : Database)
    (name : Identifier) (unique : Bool) (tableName : Identifier)
    (terms : List Syntax.OrderTerm) (filter : Option Syntax.Expr) : Prop :=
  ∃ position table keys resolvedFilter,
    database.catalog.findTable tableName = some (position, table) ∧
    reservedName tableName = false ∧ reservedName name = false ∧ database.catalog.find name = none ∧
    indexKeys context.profile.dqsDdl (Scope.single tableName table.columns !table.withoutRowid) table.columns terms = .ok keys ∧
    indexFilter context.profile.dqsDdl (Scope.single tableName table.columns !table.withoutRowid) filter = .ok resolvedFilter ∧
    (unique = true → LiteralData.uniqueRows
      ({ table := position, keys, unique, filter := resolvedFilter } : CatalogIndex).uniqueKey
      (database.rows.getD position []) = true)

end Belay.Sqlite.Model
