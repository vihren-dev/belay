import Belay.Sqlite.Model.OutlineDatabaseLaws

set_option doc.verso true

/-! The unique keys that a rename keeps. The unique keys of a table are the keys of its primary
key and its UNIQUE constraints, with the collations of their columns, and the unique indexes on it.
A rename changes no position and no collation, so the keys of a table after a rename are the keys
before it, and a database with the rows of a database with unique keys has unique keys. -/

namespace Belay.Sqlite.Model

/-- For every tables with one shape after {lit}`CatalogTable.blankNames`: the same collation for
the column at each position. Proof sketch: the lists of collations are the collations of the
blanked column lists, which are equal. -/
theorem CatalogTable.collations_of_blankNames {first second : CatalogTable}
    (same : first.blankNames = second.blankNames) :
    first.columns.map (·.collation) = second.columns.map (·.collation) := by
  have columns := congrArg (fun table => table.columns.map (·.collation)) same
  simpa [CatalogTable.blankNames, Function.comp_def, CatalogColumn.blankNames] using columns

/-- For every function whose value depends on a mapped form of its argument only, and every two
lists with one mapped form: the lists give one list of values. Proof sketch: the list of values is
the list of values of the mapped list ({name}`List.filterMap_map`). -/
theorem List.filterMap_of_map_eq {first second : List α} {g : α → β} {h : β → Option γ} {f : α → Option γ}
    (depends : ∀ item, f item = h (g item)) (same : first.map g = second.map g) :
    first.filterMap f = second.filterMap f := by
  have rewritten : f = h ∘ g := funext depends
  rw [rewritten, ← List.filterMap_map, ← List.filterMap_map, same]

/-- For every catalogs with one outline, position and tables with one shape after
{lit}`CatalogTable.blankNames`: the new catalog has the unique keys ({name}`Catalog.uniqueKeys`)
that the old catalog has. Proof sketch: the primary key, the UNIQUE constraints and the collations
of the columns are not blanked, and the unique indexes of a catalog depend on the outline only. -/
theorem Catalog.uniqueKeys_of_outline {old new : Catalog} (same : new.outline = old.outline) (position : Nat)
    {first second : CatalogTable} (shapes : first.blankNames = second.blankNames) :
    new.uniqueKeys position second = old.uniqueKeys position first := by
  have primary := congrArg (fun table => table.primaryKey) shapes
  have unique := congrArg (fun table => table.uniqueKeys) shapes
  have collations := CatalogTable.collations_of_blankNames shapes
  simp only [CatalogTable.blankNames] at primary unique
  have keyOf : UniqueKey.ofColumns second.columns = UniqueKey.ofColumns first.columns := by
    funext positions
    simp only [UniqueKey.ofColumns, ← List.getElem?_map, collations]
  let indexKey : CatalogOutline → Option UniqueKey := fun outline => match outline with
    | .index definition => if definition.table == position && definition.unique then some definition.uniqueKey else none
    | .table _ | .view | .trigger => none
  unfold Catalog.uniqueKeys
  rw [primary, unique, keyOf]
  congr 1
  refine List.filterMap_of_map_eq (g := fun object : CatalogObject => object.entry.outline) (h := indexKey) ?_ same
  intro object
  rcases object with ⟨_, entry⟩
  cases entry <;> rfl

/-- For every database that has unique keys in every table ({name}`Database.KeysUnique`) and every
catalog with the outline of its catalog: the database with that catalog has unique keys. Proof
sketch: a table of the new database has the rows of a table of the old one and the same keys
({name}`Catalog.uniqueKeys_of_outline`). -/
theorem Database.KeysUnique.of_outline {database : Database} (unique : database.KeysUnique) {renamed : Catalog}
    (same : renamed.outline = database.catalog.outline) :
    ({ database with catalog := renamed } : Database).KeysUnique := by
  intro position second found
  obtain ⟨first, present, rows, shapes⟩ := Database.table_of_outline same found
  have kept := unique position first present
  simp only [Table.KeysUnique, rows] at kept ⊢
  rw [Catalog.uniqueKeys_of_outline same position shapes]
  exact kept

end Belay.Sqlite.Model
