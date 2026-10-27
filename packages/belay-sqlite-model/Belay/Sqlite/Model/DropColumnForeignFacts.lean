import Belay.Sqlite.Model.DropColumnReferenceLaws

set_option doc.verso true

/-! The independent foreign-key facts after ALTER TABLE DROP COLUMN (ADR 0019, D4). A database that holds its row
references and has compatible parent schemas keeps both when the model runs a DROP COLUMN. The facts are stated
under the mapping of the catalog of the statement; neither of them is part of {lit}`Database.Valid`. -/

namespace Belay.Sqlite.Model

/-- For every link and function: moving the child positions of a parent link keeps whether it is located. Proof
sketch: each constructor of the link keeps its own classification when the positions move. -/
@[simp] theorem ParentLink.isLocated_mapChildren (link : ParentLink) (move : Nat → Nat) :
    (link.mapChildren move).isLocated = link.isLocated := by
  cases link <;> rfl

/-- For every database, position and index that the model runs as a DROP COLUMN with the catalog after the drop, and
every database that holds its row references: the database with the rows without the cell holds the row references of
the catalog after the drop. Proof sketch: a foreign key after the drop comes from one before it
({name}`Database.foreignKey_of_drop`), and a row finds its parent by the same cells in the same parent rows
({name}`ForeignKeyLink.satisfied_mapChildren`). -/
theorem Database.RowReferencesHold.dropColumn_catalog {database : Database} {position index : Nat}
    (holds : database.RowReferencesHold database.catalog.foreignKeyMapping)
    (ok : database.catalog.droppable position index = true) :
    (database.dropColumn position index (database.catalog.dropColumn position index)).RowReferencesHold
      (database.catalog.dropColumn position index).foreignKeyMapping := by
  intro place after found key' member row' rowMember
  obtain ⟨before, beforeFound, key, inKeys, move, rfl, linked, away, rows⟩ := Database.foreignKey_of_drop ok found member
  obtain ⟨row, inRows, cells⟩ := rows row' rowMember
  refine (ForeignKeyLink.satisfied_mapChildren (old := database) (link := database.catalog.foreignKeyMapping.link place key)
    (oldRow := row) (move := move) rfl linked cells ?_ ?_).trans (holds place before beforeFound key inKeys row inRows)
  · intro parent chosen located
    exact Catalog.parentLink_children database.catalog key located _ rfl
  · intro parent chosen located
    have different := away parent chosen located
    refine ⟨Catalog.tableAt_dropColumn_other _ index different, ?_⟩
    obtain ⟨shape, shapeFound, _⟩ := Catalog.droppable_spec ok
    unfold Database.rowsAt
    rw [Database.table_dropColumn database shapeFound parent]
    simp [Ne.symm different]

/-- For every database and position and index that the model runs as a DROP COLUMN, and every database with
compatible parent schemas: the database with the rows without the cell has compatible parent schemas under the
mapping of the catalog after the drop. Proof sketch: a foreign key after the drop comes from one before it
({name}`Database.foreignKey_of_drop`) and finds the same parent, which is located as before. -/
theorem Database.ParentSchemasCompatible.dropColumn_catalog {database : Database} {position index : Nat}
    (compatible : database.ParentSchemasCompatible database.catalog.foreignKeyMapping)
    (ok : database.catalog.droppable position index = true) :
    (database.dropColumn position index (database.catalog.dropColumn position index)).ParentSchemasCompatible
      (database.catalog.dropColumn position index).foreignKeyMapping := by
  intro place after found key' member
  obtain ⟨before, beforeFound, key, inKeys, move, rfl, linked, _, _⟩ := Database.foreignKey_of_drop ok found member
  have located := (compatible place before beforeFound key inKeys).1
  exact ⟨by simpa [Catalog.foreignKeyMapping, linked] using located, rfl⟩

/-- For every database that holds its row references, and every position, index and catalog that the model runs as a
DROP COLUMN: the database after the drop holds the row references of the stored catalog. Proof sketch:
{name}`Database.RowReferencesHold.dropColumn_catalog`, then the stored catalog has the outline and the selected
parents of the catalog after the drop ({name}`Database.RowReferencesHold.of_outline`). -/
theorem Database.RowReferencesHold.dropColumn {database : Database} {position index : Nat} {stored : Catalog}
    (holds : database.RowReferencesHold database.catalog.foreignKeyMapping)
    (runs : database.runsDropColumn position index stored = true) :
    (database.dropColumn position index stored).RowReferencesHold stored.foreignKeyMapping := by
  obtain ⟨_, outline, parents⟩ := Database.runsDropColumn_spec runs
  exact Database.RowReferencesHold.of_outline (database := database.dropColumn position index
    (database.catalog.dropColumn position index))
    (holds.dropColumn_catalog (Bool.and_eq_true_iff.mp runs).1) outline parents

/-- For every database with compatible parent schemas, and every position, index and catalog that the model runs as a
DROP COLUMN: the database after the drop has compatible parent schemas under the mapping of the stored catalog. Proof
sketch: {name}`Database.ParentSchemasCompatible.dropColumn_catalog`, then
{name}`Database.ParentSchemasCompatible.of_outline`. -/
theorem Database.ParentSchemasCompatible.dropColumn {database : Database} {position index : Nat} {stored : Catalog}
    (compatible : database.ParentSchemasCompatible database.catalog.foreignKeyMapping)
    (runs : database.runsDropColumn position index stored = true) :
    (database.dropColumn position index stored).ParentSchemasCompatible stored.foreignKeyMapping := by
  obtain ⟨_, outline, parents⟩ := Database.runsDropColumn_spec runs
  exact Database.ParentSchemasCompatible.of_outline (database := database.dropColumn position index
    (database.catalog.dropColumn position index))
    (compatible.dropColumn_catalog (Bool.and_eq_true_iff.mp runs).1) outline parents

end Belay.Sqlite.Model
