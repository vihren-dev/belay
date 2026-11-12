import Belay.Sqlite.Model.Queries.Preparation.InsertSelectKeeps
import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyStatement

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For any supplied mapping compatible with a database's parent schemas, row truth
under that mapping is equivalent to row truth under the catalog-selected mapping. Empty
child tables still require schema compatibility. Proof sketch: compatibility equates each
declared parent comparison; substitute it in both directions of the row fact. -/
theorem Database.ParentSchemasCompatible.rowReferences_iff_selected {database : Database} {mapping : ForeignKeyMapping}
    (compatible : database.ParentSchemasCompatible mapping) :
    database.RowReferencesHold mapping ↔ database.RowReferencesHold database.catalog.foreignKeyMapping := by
  constructor <;> intro holds position table found key declared row member
  all_goals
    have same := (compatible position table found key declared).2
    simpa only [ForeignKeyMapping.link, Catalog.foreignKeyMapping, same] using holds position table found key declared row member

end Belay.Sqlite.Model
