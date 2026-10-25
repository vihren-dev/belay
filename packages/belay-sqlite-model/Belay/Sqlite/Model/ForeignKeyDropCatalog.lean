import Belay.Sqlite.Model.ForeignKeyDropEngine
import Belay.Sqlite.Model.ForeignKeySchemaWrites

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- A catalog-dependent schema fact has row-write laws because those operations keep the catalog. -/
private theorem catalogSchemaWriteLaws (mapping : Catalog → ForeignKeyMapping) :
    WriteLaws (fun database => database.ParentSchemasCompatible (mapping database.catalog)) where
  sublist _ _ _ holds _ := holds.catalog_eq rfl
  write _ _ _ _ holds _ _ _ := holds.catalog_eq rfl

/-- For any mapping family and enforced DROP, compatible parent schemas survive success and
partial FAIL if each surviving declaration's mapping and selected parent transport through
the catalog removal. Removed children impose nothing. Triggers, actions, stored rows and
rule enforcement are unrestricted. Other error carriers impose nothing. Proof sketch: the
existing DROP invariant retains the catalog during implicit DELETE; apply the independent
schema transport law only when that DELETE succeeds and catalog removal occurs. -/
theorem dropKeys_parentSchemasCompatible (mapping : Catalog → ForeignKeyMapping) (rules : Resolved.WriteRules)
    (clock : Int) (positions : List Nat) {database : Database}
    (holds : database.ParentSchemasCompatible (mapping database.catalog))
    (moved : ∀ child shape, database.catalog.tableAt child = some shape → !positions.contains child →
      ∀ key ∈ shape.allForeignKeys,
        (mapping (database.catalog.drop positions)).parent (keptBelow positions child) key =
          ((mapping database.catalog).parent child key).transport (keptBelow positions))
    (selection : ∀ child shape, database.catalog.tableAt child = some shape → !positions.contains child →
      ∀ key ∈ shape.allForeignKeys,
        (database.catalog.drop positions).parentLink key =
          (database.catalog.parentLink key).transport (keptBelow positions)) :
    (dropKeys rules clock positions database).effect.Satisfies
      (fun result => result.ParentSchemasCompatible (mapping result.catalog)) := by
  apply Effect.satisfies_of_effectDatabase
  apply dropKeys_holds (catalogSchemaWriteLaws mapping) rules clock positions holds
  intro other same compatible
  apply compatible.drop positions _
  · intro child table present kept key declared
    have found := KeyState.table_shape (state := {rows := other.rows}) present
    rw [same] at found
    simpa only [Database.drop, same] using moved child table.shape found kept key declared
  · intro child table present kept key declared
    have found := KeyState.table_shape (state := {rows := other.rows}) present
    rw [same] at found
    simpa only [same] using selection child table.shape found kept key declared

/-- Actual resolved enforced DROP preserves parent-schema compatibility on success and partial
FAIL under initial compatibility and separate mapping/selection transport for every surviving
child declaration. Removed children and other error carriers require nothing. Proof sketch:
resolved execution uses the existing DROP engine and its schema preservation law. -/
theorem runStatement_drop_enforced_parentSchemasCompatible (mapping : Catalog → ForeignKeyMapping)
    (rules : Resolved.WriteRules) (clock : Int) (counters : Counters) (parameters : List Value)
    (positions : List Nat) {database : Database}
    (holds : database.ParentSchemasCompatible (mapping database.catalog))
    (moved : ∀ child shape, database.catalog.tableAt child = some shape → !positions.contains child →
      ∀ key ∈ shape.allForeignKeys,
        (mapping (database.catalog.drop positions)).parent (keptBelow positions child) key =
          ((mapping database.catalog).parent child key).transport (keptBelow positions))
    (selection : ∀ child shape, database.catalog.tableAt child = some shape → !positions.contains child →
      ∀ key ∈ shape.allForeignKeys,
        (database.catalog.drop positions).parentLink key =
          (database.catalog.parentLink key).transport (keptBelow positions)) :
    (runStatement clock counters parameters (.drop positions (some rules)) database).effect.Satisfies
      (fun result => result.ParentSchemasCompatible (mapping result.catalog)) :=
  dropKeys_parentSchemasCompatible mapping rules clock positions holds moved selection

/-- Both selected atoms survive enforced DROP on success and partial FAIL when the input has
both, the actual row engine meets its intermediate-write conditions, and every surviving
declaration's selected parent transports and remains in the catalog. Thus this sufficient
combined rule covers retained-parent drops; dropping a referenced parent can preserve only
the row atom through the NULL case of {name}`dropKeys_rowReferences`. Other error carriers
require nothing. Proof sketch: combine the two atom laws, deriving the retained-parent frame
from unchanged row-engine catalogs. -/
theorem runStatement_drop_enforced_foreignKeyAtoms {profile : Profile} (rules : Resolved.WriteRules)
    (clock : Int) (counters : Counters) (parameters : List Value) (positions : List Nat)
    {database : Database} (ready : database.ForeignKeyReady profile)
    (holds : database.ParentSchemasCompatible database.catalog.foreignKeyMapping ∧
      database.RowReferencesHold database.catalog.foreignKeyMapping)
    (conditions : rules.ForeignKeyConditions profile database.catalog)
    (selection : ∀ child shape, database.catalog.tableAt child = some shape → !positions.contains child →
      ∀ key ∈ shape.allForeignKeys, (database.catalog.drop positions).parentLink key =
        (database.catalog.parentLink key).transport (keptBelow positions))
    (parents : ∀ child shape, database.catalog.tableAt child = some shape → !positions.contains child →
      ∀ key ∈ shape.allForeignKeys, ∀ parent comparison,
        database.catalog.parentLink key = .located parent comparison → !positions.contains parent) :
    (runStatement clock counters parameters (.drop positions (some rules)) database).effect.Satisfies
      (fun result => result.ParentSchemasCompatible result.catalog.foreignKeyMapping ∧
        result.RowReferencesHold result.catalog.foreignKeyMapping) := by
  have frame (after : Database) (same : after.catalog = database.catalog) :
      after.DropForeignKeyFrame positions after.catalog.foreignKeyMapping
        (after.catalog.drop positions).foreignKeyMapping := by
    intro child table present kept key declared
    have found := KeyState.table_shape (state := {rows := after.rows}) present
    rw [same] at found
    right
    simpa only [Catalog.foreignKeyMapping, ForeignKeyMapping.parent, same] using
      And.intro (selection child table.shape found kept key declared) (parents child table.shape found kept key declared)
  intro after carried
  refine ⟨runStatement_drop_enforced_parentSchemasCompatible Catalog.foreignKeyMapping rules clock counters
    parameters positions holds.1 selection selection after carried, ?_⟩
  apply runStatement_drop_enforced_rowReferences rules clock counters parameters positions ready holds.2 conditions
    ?_ (fun _ => frame database rfl) after carried
  intro target table _ _ deleted ran
  apply frame deleted
  exact keyRun_ok_catalog ran

end Belay.Sqlite.Model
