import Belay.Sqlite.Model.OutlineForeignKeyLaws
import Belay.Sqlite.Model.OutlineDatabaseLaws

set_option doc.verso true

/-! The parents that the foreign keys of a renamed catalog select. The run of a rename stores
the new catalog only when its outline and its selected parents ({lit}`Catalog.selectedParents`) equal
those of the old catalog. A key of a table of the new database then matches a key of the old table
with the same columns and the same parent, so the row references and the parent schema facts that
the old database has hold again. -/

namespace Belay.Sqlite.Model

/-- For every catalog and position with a table: the selected parents at the position are the
parents that the keys of the table select. Proof sketch: both lists read the same object of the
catalog at the position. -/
theorem Catalog.selectedParents_tableAt {catalog : Catalog} {position : Nat} {shape : CatalogTable}
    (found : catalog.tableAt position = some shape) :
    catalog.selectedParents[position]? = some (shape.allForeignKeys.map catalog.parentLink) := by
  unfold Catalog.tableAt at found
  unfold Catalog.selectedParents
  rw [List.getElem?_map]
  cases object : catalog[position]? with
  | none => simp [object] at found
  | some entry =>
    rcases entry with ⟨_, entry⟩
    cases entry <;> simp_all

/-- For every database and catalog with its outline and selected parents, a table of the database
with the catalog and a foreign key of it: the table of the database at the same position has a
foreign key with the same columns that selects the same parent in the catalog of the database, and
the table has the same rows. Proof sketch: the selected parents are equal at the position
({name}`Catalog.selectedParents_tableAt`), and the keys correspond by place
({name}`CatalogTable.foreignKey_of_blankNames`). -/
theorem Database.foreignKey_of_outline {database : Database} {renamed : Catalog}
    (same : renamed.outline = database.catalog.outline) (parents : renamed.selectedParents = database.catalog.selectedParents)
    {position : Nat} {second : Table}
    (found : ({ database with catalog := renamed } : Database).table position = some second)
    {key : ForeignKey} (member : key ∈ second.shape.allForeignKeys) :
    ∃ first, database.table position = some first ∧ second.rows = first.rows ∧
      ∃ other ∈ first.shape.allForeignKeys, other.columns = key.columns ∧
        database.catalog.parentLink other = renamed.parentLink key := by
  obtain ⟨first, present, rows, shapes⟩ := Database.table_of_outline same found
  refine ⟨first, present, rows, ?_⟩
  have newShape : renamed.tableAt position = some second.shape := by
    unfold Database.table at found
    cases shape : renamed.tableAt position with
    | none => simp [shape] at found
    | some other =>
      simp only [shape, Option.map_some, Option.some.injEq] at found
      subst found
      rfl
  have oldShape : database.catalog.tableAt position = some first.shape := by
    unfold Database.table at present
    cases shape : database.catalog.tableAt position with
    | none => simp [shape] at present
    | some other =>
      simp only [shape, Option.map_some, Option.some.injEq] at present
      subst present
      rfl
  have selected := Catalog.selectedParents_tableAt newShape
  rw [parents, Catalog.selectedParents_tableAt oldShape, Option.some.injEq] at selected
  obtain ⟨other, otherMember, blanked, linked⟩ :=
    CatalogTable.foreignKey_of_blankNames shapes selected.symm member
  exact ⟨other, otherMember, ForeignKey.columns_of_blankNames blanked, linked⟩

/-- For every database whose rows hold their selected row references, and every catalog with its
outline and selected parents: the database with that catalog holds the row references of that
catalog's selection ({name}`Database.RowReferencesHold`). Proof sketch: a key of the new table
matches a key of the old table with the same columns and the same parent
({name}`Database.foreignKey_of_outline`), and the row is looked up in the same rows
({name}`ForeignKeyLink.satisfied_of_outline`). -/
theorem Database.RowReferencesHold.of_outline {database : Database}
    (holds : database.RowReferencesHold database.catalog.foreignKeyMapping) {renamed : Catalog}
    (same : renamed.outline = database.catalog.outline) (parents : renamed.selectedParents = database.catalog.selectedParents) :
    ({ database with catalog := renamed } : Database).RowReferencesHold renamed.foreignKeyMapping := by
  intro position second found key member row rowMember
  obtain ⟨first, present, rows, other, otherMember, columns, linked⟩ :=
    Database.foreignKey_of_outline same parents found member
  rw [rows] at rowMember
  have kept := holds position first present other otherMember row rowMember
  rw [← kept]
  exact ForeignKeyLink.satisfied_of_outline same (firstLink := database.catalog.foreignKeyMapping.link position other)
    columns.symm (by simp [ForeignKeyMapping.link, Catalog.foreignKeyMapping, linked]) row

/-- For every database with compatible parent schemas under its selected mapping, and every
catalog with its outline and selected parents: the database with that catalog has compatible parent
schemas under the mapping of that catalog ({name}`Database.ParentSchemasCompatible`). Proof sketch:
a key of the new table selects the parent of a key of the old table
({name}`Database.foreignKey_of_outline`), so it is located as that one is. -/
theorem Database.ParentSchemasCompatible.of_outline {database : Database}
    (compatible : database.ParentSchemasCompatible database.catalog.foreignKeyMapping) {renamed : Catalog}
    (same : renamed.outline = database.catalog.outline) (parents : renamed.selectedParents = database.catalog.selectedParents) :
    ({ database with catalog := renamed } : Database).ParentSchemasCompatible renamed.foreignKeyMapping := by
  intro position second found key member
  obtain ⟨first, present, _, other, otherMember, _, linked⟩ :=
    Database.foreignKey_of_outline same parents found member
  have kept := (compatible position first present other otherMember).1
  simp only [Catalog.foreignKeyMapping] at kept ⊢
  exact ⟨by rw [← linked]; exact kept, trivial⟩

end Belay.Sqlite.Model
