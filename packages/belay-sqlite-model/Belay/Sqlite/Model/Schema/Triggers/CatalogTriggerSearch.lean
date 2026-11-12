import Belay.Sqlite.Model.Schema.Columns.ModelProjectionLaws
import Belay.Sqlite.Model.Schema.Ddl.CatalogValidSet
import Belay.Sqlite.Model.Queries.Preparation.CatalogTriggerSearch

set_option doc.verso true

/-! CREATE TRIGGER and the name search of a catalog. A trigger is appended after every other object
and is not in the namespace of tables, so a search for a table by name finds what it found before. -/

namespace Belay.Sqlite.Model

/-- For every catalog, table name, trigger name and trigger: the lookup of the table by name after
{name}`Catalog.createTrigger` gives what it gave before. In plain words, creating a trigger changes
no table lookup, whatever the names. Proof sketch: the search finds the same first match in the old
prefix, or finds none in it and none at the appended trigger ({name}`findPosition_append`,
{name}`findPosition_append_rejected`). -/
theorem Catalog.findTable_createTrigger (catalog : Catalog) (name triggerName : Identifier)
    (trigger : CatalogTrigger) :
    (catalog.createTrigger triggerName trigger).findTable name = catalog.findTable name := by
  unfold Catalog.findTable Catalog.find Catalog.createTrigger
  cases located : findPosition (fun object => object.name.sameName name && !object.isTrigger) catalog with
  | some pair => rw [findPosition_append _ located]
  | none =>
    rw [findPosition_append_rejected located (by simp [CatalogObject.isTrigger, CatalogEntry.isTrigger])]

end Belay.Sqlite.Model
