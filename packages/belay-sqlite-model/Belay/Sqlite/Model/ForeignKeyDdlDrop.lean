import Belay.Sqlite.Model.ForeignKeyDropSchema
import Belay.Sqlite.Model.RowLocalFrame

set_option doc.verso true

/-! Plain DROP preserves supplied row comparisons and schema compatibility under separate
transport conditions. The implicit DELETE used by enforced DROP needs its row-engine law too. -/

namespace Belay.Sqlite.Model

/-- For any catalog-dependent supplied mapping, plain DROP preserves row references if
they hold initially, each surviving declaration's mapping transports, and every located
parent of a surviving child is kept. Removed children and supporting indexes impose no
condition. This is the path without an implicit row-engine DELETE. Proof sketch: the actual
statement succeeds with exactly the dropped database, so apply the independent row frame. -/
theorem runStatement_drop_rowReferences (mapping : Catalog → ForeignKeyMapping)
    (clock : Int) (counters : Counters) (parameters : List Value) {database : Database}
    (positions : List Nat) (holds : database.RowReferencesHold (mapping database.catalog))
    (moved : ∀ child table, database.table child = some table → !positions.contains child →
      ∀ key ∈ table.shape.allForeignKeys,
        (mapping (database.catalog.drop positions)).parent (keptBelow positions child) key =
          ((mapping database.catalog).parent child key).transport (keptBelow positions))
    (parents : ∀ child table, database.table child = some table → !positions.contains child →
      ∀ key ∈ table.shape.allForeignKeys, ∀ parent comparison,
        (mapping database.catalog).parent child key = .located parent comparison → !positions.contains parent) :
    (runStatement clock counters parameters (.drop positions none) database).effect.Satisfies
      (fun after => after.RowReferencesHold (mapping after.catalog)) := by
  exact Effect.satisfies_of_effectDatabase (holds.drop positions _ moved parents)

/-- For any catalog-dependent mapping, plain DROP preserves schema compatibility when
it holds initially and each surviving declaration's mapping and selected link transport.
Removed children impose nothing; removing a supporting index can fail the selection premise.
Rows are unrestricted. Proof sketch: actual execution is the catalog drop, then the schema
transport law applies. -/
theorem runStatement_drop_parentSchemasCompatible (mapping : Catalog → ForeignKeyMapping)
    (clock : Int) (counters : Counters) (parameters : List Value) {database : Database}
    (positions : List Nat) (holds : database.ParentSchemasCompatible (mapping database.catalog))
    (moved : ∀ child table, database.table child = some table → !positions.contains child →
      ∀ key ∈ table.shape.allForeignKeys,
        (mapping (database.catalog.drop positions)).parent (keptBelow positions child) key =
          ((mapping database.catalog).parent child key).transport (keptBelow positions))
    (selection : ∀ child table, database.table child = some table → !positions.contains child →
      ∀ key ∈ table.shape.allForeignKeys,
        (database.catalog.drop positions).parentLink key =
          (database.catalog.parentLink key).transport (keptBelow positions)) :
    (runStatement clock counters parameters (.drop positions none) database).effect.Satisfies
      (fun after => after.ParentSchemasCompatible (mapping after.catalog)) := by
  exact Effect.satisfies_of_effectDatabase (holds.drop positions _ moved selection)

/-- For any plain DROP, both selected FK atoms survive if both hold initially, every
surviving declaration's selected parent is kept, and its selected link transports through
the catalog edit. Removed children impose no condition. Equal ordered eligible indexes and
retained named parents are sufficient for selection transport, as proved by
{name}`Database.ParentSchemasCompatible.selection_drop`. Proof sketch: selected mapping
transport is exactly selection transport, so combine the separate atom laws. -/
theorem runStatement_drop_foreignKeyAtoms (clock : Int) (counters : Counters) (parameters : List Value)
    {database : Database} (positions : List Nat)
    (holds : database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
      database.RowReferencesHold database.catalog.foreignKeyMapping)
    (selection : ∀ child table, database.table child = some table → !positions.contains child →
      ∀ key ∈ table.shape.allForeignKeys,
        (database.catalog.drop positions).parentLink key =
          (database.catalog.parentLink key).transport (keptBelow positions))
    (parents : ∀ child table, database.table child = some table → !positions.contains child →
      ∀ key ∈ table.shape.allForeignKeys, ∀ parent comparison,
        database.catalog.parentLink key = .located parent comparison → !positions.contains parent) :
    (runStatement clock counters parameters (.drop positions none) database).effect.Satisfies
      (fun after => after.ParentSchemasCompatible after.catalog.foreignKeyMapping ∧
        after.RowReferencesHold after.catalog.foreignKeyMapping) := by
  intro after kept
  exact ⟨runStatement_drop_parentSchemasCompatible Catalog.foreignKeyMapping clock counters parameters
    positions holds.1 selection selection after kept,
    runStatement_drop_rowReferences Catalog.foreignKeyMapping clock counters parameters
      positions holds.2 selection parents after kept⟩

end Belay.Sqlite.Model
