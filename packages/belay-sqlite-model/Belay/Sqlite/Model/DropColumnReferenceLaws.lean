import Belay.Sqlite.Model.DropColumnLinkLaws
import Belay.Sqlite.Model.DropColumnDatabaseLaws
import Belay.Sqlite.Model.Resolution.ColumnDropForeignLaws
import Belay.Sqlite.Model.OutlineSelectedParentLaws

set_option doc.verso true

/-! The foreign keys of a database after ALTER TABLE DROP COLUMN (ADR 0019, D4). A foreign key of the database with
the catalog after the drop is a foreign key of the database before it, with the child columns moved, and it finds
the same parent. A row of the child table, without the cell, has its parent exactly when it had before. -/

namespace Belay.Sqlite.Model

/-- For every key: the key with its child columns mapped by the identity is the key. Proof sketch: unfolding the
mapping leaves the identity map over the child columns. -/
@[simp] theorem ForeignKey.mapColumns_id (key : ForeignKey) : key.mapColumns id = key := by
  simp [ForeignKey.mapColumns]

/-- For every database, position and index that the catalog lets the model drop, and every foreign key of a table
of the database with the catalog after the drop and the rows without the cell: the table before had a foreign key
that it came from, whose child columns were moved by a function; the key finds the same parent, with moved child
positions, which is no table at the dropped position; and each row of the table has a row before it with the same
cells at the child columns. Proof sketch: at the dropped position, the keys of the table are those of the table before
without the column ({name}`CatalogTable.mem_allForeignKeys_dropColumnAt`), moved by {lit}`dropPosition`, and the rows
lose the cell of the column, which no child column names; in every other table nothing moves. The parent comes from
{name}`Catalog.parentLink_dropColumn_mapColumns`, valid because no foreign key names the dropped table
({name}`Catalog.droppable_foreign`). -/
theorem Database.foreignKey_of_drop {database : Database} {position index : Nat}
    (ok : database.catalog.droppable position index = true) {place : Nat} {after : Table}
    (found : (database.dropColumn position index (database.catalog.dropColumn position index)).table place = some after)
    {key' : ForeignKey} (member : key' ∈ after.shape.allForeignKeys) :
    ∃ before, database.table place = some before ∧ ∃ key ∈ before.shape.allForeignKeys, ∃ move : Nat → Nat,
      key' = key.mapColumns move ∧
      (database.catalog.dropColumn position index).parentLink key' = (database.catalog.parentLink key).mapChildren move ∧
      (∀ parent found, database.catalog.parentLink key = .located parent found → parent ≠ position) ∧
      ∀ row' ∈ after.rows, ∃ row ∈ before.rows, ∀ child ∈ key.columns,
        row'.values.getD (move child) .null = row.values.getD child .null := by
  obtain ⟨shape, shapeFound, clean, _⟩ := Catalog.droppable_spec ok
  obtain ⟨object, at_position, _⟩ : ∃ object, database.catalog[position]? = some object ∧ object.entry = .table shape := by
    unfold Catalog.tableAt at shapeFound
    rcases hold : database.catalog[position]? with _ | ⟨n, e⟩
    · simp [hold] at shapeFound
    · cases e <;> simp_all
  rw [Database.table_dropColumn database shapeFound place] at found
  by_cases same : position = place
  · subst same
    simp only [↓reduceIte] at found
    obtain ⟨before, beforeFound, rfl⟩ := Option.map_eq_some_iff.mp found
    have beforeShape : before.shape = shape := by
      simp only [Database.table, shapeFound, Option.map_some, Option.some.injEq] at beforeFound
      rw [← beforeFound]
    simp only [Table.dropColumn] at member
    rw [beforeShape] at member
    obtain ⟨key, inKeys, unnamed, rfl⟩ := CatalogTable.mem_allForeignKeys_dropColumnAt clean member
    have other := Catalog.droppable_foreign ok at_position shapeFound inKeys
    refine ⟨before, beforeFound, key, beforeShape ▸ inKeys, dropPosition index, rfl,
      Catalog.parentLink_dropColumn_mapColumns database.catalog index at_position key other _, ?_, ?_⟩
    · intro parent chosen located
      exact Catalog.parentLink_position_ne at_position key other (Or.inl ⟨_, located⟩)
    · intro row' rowMember
      obtain ⟨row, inRows, rfl⟩ := List.mem_map.mp rowMember
      refine ⟨row, inRows, fun child inKey => ?_⟩
      have differs : child ≠ index := fun same => unnamed (same ▸ inKey)
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, Row.dropValue_cell,
        dropSource_dropPosition differs]
  · simp only [same, ↓reduceIte] at found
    refine ⟨after, found, key', member, id, by simp, ?_, ?_, fun row member => ⟨row, member, fun _ _ => rfl⟩⟩
    · have other := Catalog.droppable_foreign ok at_position (slot := place) ?_ member
      · simpa using Catalog.parentLink_dropColumn_mapColumns database.catalog index at_position key' other id
      · unfold Database.table at found
        cases hold : database.catalog.tableAt place with
        | none => simp [hold] at found
        | some shape' =>
          simp only [hold, Option.map_some, Option.some.injEq] at found
          subst found
          rfl
    · intro parent chosen located
      have other := Catalog.droppable_foreign ok at_position (slot := place) (table := after.shape) ?_ member
      · exact Catalog.parentLink_position_ne at_position key' other (Or.inl ⟨_, located⟩)
      · unfold Database.table at found
        cases hold : database.catalog.tableAt place with
        | none => simp [hold] at found
        | some shape' =>
          simp only [hold, Option.map_some, Option.some.injEq] at found
          subst found
          rfl

end Belay.Sqlite.Model
