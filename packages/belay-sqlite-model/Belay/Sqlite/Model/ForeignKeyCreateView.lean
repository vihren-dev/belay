import Belay.Sqlite.Model.ForeignKeyDdlConditions

set_option doc.verso true

/-! CREATE VIEW and the selected parent of a foreign key. A view stores no rows and no foreign
keys. It changes a parent link only when a foreign key names it: a name that found no table or
view now finds the view, which is a mismatch. -/

namespace Belay.Sqlite.Model

/-- For every test, list and appended item that the test rejects: the search over the longer
list finds what the search over the list finds. Proof sketch: a hit in the list stays
({name}`findPosition_append`); with no hit, the search reaches the rejected item and finds
nothing. -/
theorem findPosition_append_single_rejected {α : Type} {test : α → Bool} (items : List α) {item : α}
    (rejected : test item = false) :
    findPosition test (items ++ [item]) = findPosition test items := by
  induction items with
  | nil => simp [findPosition, rejected]
  | cons head rest ih =>
    by_cases hit : test head = true
    · simp [findPosition, hit]
    · simp only [List.cons_append, findPosition, hit, Bool.false_eq_true, ↓reduceIte, ih]

/-- For every catalog, view and foreign key whose referenced table name is not the name of the view:
the catalog with the view appended gives the key the parent link that the catalog gives. Proof
sketch: the name lookup skips the appended view ({name}`findPosition_append_single_rejected`), and a view
adds no index to the parent keys. -/
theorem Catalog.parentLink_createView_of_other_name (catalog : Catalog) (name : Identifier) (view : CatalogView)
    (key : ForeignKey) (other : name.sameName key.table = false) :
    (catalog.createView name view).parentLink key = catalog.parentLink key := by
  have lookup : (catalog.createView name view).find key.table = catalog.find key.table := by
    unfold Catalog.find Catalog.createView
    exact findPosition_append_single_rejected catalog (by simp [other])
  have tables : (catalog.createView name view).findTable key.table = catalog.findTable key.table := by
    unfold Catalog.findTable
    rw [lookup]
  have views : (catalog.createView name view).findView key.table = catalog.findView key.table := by
    unfold Catalog.findView
    rw [lookup]
  have indexes (position : Nat) (shape : CatalogTable) :
      (catalog.createView name view).parentKey position shape key = catalog.parentKey position shape key := by
    simp [Catalog.parentKey, Catalog.parentIndexes, Catalog.createView, List.filterMap_append]
  unfold Catalog.parentLink
  rw [tables, views]
  cases catalog.findTable key.table with
  | none => rfl
  | some pair => simp only [indexes]

/-- For every catalog and view: CREATE VIEW keeps the selected parent of every old declaration
when no declaration of a table names the view. Proof sketch: apply
{name}`Catalog.parentLink_createView_of_other_name` to each declaration. -/
theorem Catalog.createKeepsSelection_view (catalog : Catalog) (name : Identifier) (view : CatalogView)
    (unnamed : ∀ position shape, catalog.tableAt position = some shape → ∀ key ∈ shape.allForeignKeys,
      name.sameName key.table = false) :
    catalog.CreateKeepsSelection {name, entry := .view view} := fun position shape found key declared =>
  Catalog.parentLink_createView_of_other_name catalog name view key (unnamed position shape found key declared)

end Belay.Sqlite.Model
