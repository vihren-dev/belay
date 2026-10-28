import Belay.Sqlite.Model.ModelProjectionLaws
import Belay.Sqlite.Model.CatalogValidSet

set_option doc.verso true

/-! CREATE TRIGGER and the name search of a catalog. A trigger is appended after every other object
and is not in the namespace of tables, so a search for a table by name finds what it found before. -/

namespace Belay.Sqlite.Model

/-- For every test, list and item: if the test finds no element of the list and rejects the item,
it finds no element of the list with the item appended. In plain words, appending a rejected item
cannot create a match. Proof sketch: induction on the list; the head is rejected, as is the appended
item. -/
theorem findPosition_append_rejected {α : Type} {test : α → Bool} {items : List α} {item : α}
    (absent : findPosition test items = none) (rejected : test item = false) :
    findPosition test (items ++ [item]) = none := by
  induction items with
  | nil => simp [findPosition, rejected]
  | cons head rest ih =>
    by_cases hit : test head = true
    · simp [findPosition, hit] at absent
    · have restAbsent : findPosition test rest = none := by simpa [findPosition, hit] using absent
      simpa [findPosition, hit] using ih restAbsent

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
