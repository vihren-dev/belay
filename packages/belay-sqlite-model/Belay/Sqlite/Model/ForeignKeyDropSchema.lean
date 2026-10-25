import Belay.Sqlite.Model.ForeignKeyDropFrame
import Belay.Sqlite.Model.CatalogValidDrop

set_option doc.verso true

/-! Parent-schema compatibility through DROP, separately from row-reference transport.
The selected key must survive; retaining child and parent rows alone does not establish it. -/

namespace Belay.Sqlite.Model

/-- For any named parent found before a drop, keeping its position and its ordered eligible
indexes preserves the selected link with its position transported. This applies both to a
located comparison and a mismatch. Proof sketch: exact named lookup preserves the parent
definition, then equal index inputs preserve the existing key selector. -/
theorem Catalog.parentLink_drop_of_indexes {catalog : Catalog} {positions : List Nat}
    {key : ForeignKey} {parent : Nat} {shape : CatalogTable}
    (found : catalog.findTable key.table = some (parent, shape))
    (kept : !positions.contains parent)
    (indexes : (catalog.drop positions).parentIndexes (keptBelow positions parent) shape =
      catalog.parentIndexes parent shape) :
    (catalog.drop positions).parentLink key =
      (catalog.parentLink key).transport (keptBelow positions) := by
  have selected : (catalog.drop positions).parentKey (keptBelow positions parent) shape key =
      catalog.parentKey parent shape key := by
    simp only [Catalog.parentKey, indexes]
  simp only [Catalog.parentLink, Catalog.findTable_drop_kept found kept, found, selected]
  cases catalog.parentKey parent shape key <;> rfl

/-- For any database with compatible parent schemas, dropping objects preserves compatibility
under a transported mapping when each surviving declaration's supplied mapping and catalog
selection transport together. Removed child tables impose no condition. Rows are unrestricted;
dropping a supporting index can violate the selection premise. Proof sketch: every remaining
table is an old table at its transported position, and transport retains located comparisons. -/
theorem Database.ParentSchemasCompatible.drop {database : Database} {mapping : ForeignKeyMapping}
    (holds : database.ParentSchemasCompatible mapping) (positions : List Nat) (transported : ForeignKeyMapping)
    (mappingMoved : ∀ child table, database.table child = some table → !positions.contains child →
      ∀ key ∈ table.shape.allForeignKeys,
        transported.parent (keptBelow positions child) key = (mapping.parent child key).transport (keptBelow positions))
    (selection : ∀ child table, database.table child = some table → !positions.contains child →
      ∀ key ∈ table.shape.allForeignKeys,
        (database.catalog.drop positions).parentLink key =
          (database.catalog.parentLink key).transport (keptBelow positions)) :
    (database.drop positions).ParentSchemasCompatible transported := by
  intro position table present key declared
  obtain ⟨old, kept, rfl, found⟩ := Database.table_drop_cases present
  have previous := holds old table found key declared
  change (transported.parent (keptBelow positions old) key).isLocated = true ∧
    transported.parent (keptBelow positions old) key = (database.catalog.drop positions).parentLink key
  rw [mappingMoved old table found kept key declared, selection old table found kept key declared]
  refine ⟨?_, congrArg (ParentLink.transport (keptBelow positions)) previous.2⟩
  have located := previous.1
  cases selected : mapping.parent old key with
  | located => rfl
  | missing | mismatch => simp only [selected, ParentLink.isLocated, Bool.false_eq_true] at located

/-- If a database has compatible parent schemas, keeping each surviving declaration's
named parent and ordered eligible indexes is sufficient for its selected link to transport
through DROP. Dropped child tables impose nothing. Proof sketch: compatibility rules out an
absent parent; apply the exact lookup and index frame to the found parent. -/
theorem Database.ParentSchemasCompatible.selection_drop {database : Database} {mapping : ForeignKeyMapping}
    (holds : database.ParentSchemasCompatible mapping) (positions : List Nat)
    (parents : ∀ child table, database.table child = some table → !positions.contains child →
      ∀ key ∈ table.shape.allForeignKeys, ∀ parent shape,
        database.catalog.findTable key.table = some (parent, shape) →
        !positions.contains parent ∧
        (database.catalog.drop positions).parentIndexes (keptBelow positions parent) shape =
          database.catalog.parentIndexes parent shape) :
    ∀ child table, database.table child = some table → !positions.contains child →
      ∀ key ∈ table.shape.allForeignKeys,
        (database.catalog.drop positions).parentLink key =
          (database.catalog.parentLink key).transport (keptBelow positions) := by
  intro child table present kept key declared
  have previous := holds child table present key declared
  cases found : database.catalog.findTable key.table with
  | none =>
    rw [previous.2] at previous
    cases view : database.catalog.findView key.table with
    | none => simp [Catalog.parentLink, found, view, ParentLink.isLocated] at previous
    | some pair =>
      obtain ⟨position, _⟩ := pair
      simp [Catalog.parentLink, found, view, ParentLink.isLocated] at previous
  | some pair =>
    obtain ⟨parent, shape⟩ := pair
    have facts := parents child table present kept key declared parent shape found
    exact Catalog.parentLink_drop_of_indexes found facts.1 facts.2

end Belay.Sqlite.Model
