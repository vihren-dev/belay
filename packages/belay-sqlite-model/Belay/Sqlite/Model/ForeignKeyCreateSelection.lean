import Belay.Sqlite.Model.CatalogValidLaws
import Belay.Sqlite.Model.ForeignKeyFacts

set_option doc.verso true

/-! Appending catalog objects cannot replace a parent key that the old catalog already
selects. This supplies the common CREATE schema premise from the input schema atom. -/

namespace Belay.Sqlite.Model

/-- For any catalog extension, parent shape, position and foreign key, a parent key already
selected remains selected. Proof sketch: appended indexes follow the old indexes, so each
first successful search keeps its result; the rowid-alias shortcut does not read the catalog. -/
theorem Catalog.parentKey_append_of_some {catalog : Catalog} (extension : Catalog)
    {position : Nat} {shape : CatalogTable} {key : ForeignKey} {comparison : ParentKey}
    (selected : catalog.parentKey position shape key = some comparison) :
    (catalog ++ extension).parentKey position shape key = some comparison := by
  have grows : ∃ suffix, (catalog ++ extension).parentIndexes position shape =
      catalog.parentIndexes position shape ++ suffix := by
    refine ⟨extension.parentIndexes position {shape with primaryKey := [], uniqueKeys := []}, ?_⟩
    simp only [Catalog.parentIndexes, List.filterMap_append, List.append_assoc]
    simp
  obtain ⟨suffix, grows⟩ := grows
  let pick (indexes : List (Bool × List (Nat × Collation))) : Option ParentKey :=
    if key.referenced.isEmpty then
      (indexes.find? (·.1)).bind fun (_, index) =>
        if index.length == key.columns.length then some (.columns (key.columns.zip (index.map (·.1)))) else none
    else (indexes.findSome? fun (_, index) => matchIndex shape key index).map .columns
  have keep : ∀ named : Bool,
      (if key.columns.length == 1 && named then some ParentKey.rowid else pick (catalog.parentIndexes position shape)) = some comparison →
      (if key.columns.length == 1 && named then some ParentKey.rowid else pick ((catalog ++ extension).parentIndexes position shape)) = some comparison := by
    intro named selected
    split at selected
    · rename_i enabled
      simpa only [enabled, ↓reduceIte] using selected
    · rename_i disabled
      simp only [disabled, pick, grows] at selected ⊢
      split at selected
      · rename_i implicitKey
        simp only [implicitKey, ↓reduceIte, List.find?_append]
        cases found : (catalog.parentIndexes position shape).find? (·.1) with
        | none => simp [found] at selected
        | some pair => simpa [found] using selected
      · rename_i explicitKey
        simp only [explicitKey, List.findSome?_append]
        cases found : (catalog.parentIndexes position shape).findSome? (fun (_, index) => matchIndex shape key index) with
        | none => simp [found] at selected
        | some pairs => simpa [found] using selected
  apply keep
  exact selected

/-- For any extension and foreign key with a located parent comparison, catalog append
keeps that exact parent and comparison. Missing or mismatched parents are excluded. Proof
sketch: append keeps the first named-table lookup and its already-selected parent key. -/
theorem Catalog.parentLink_append_of_located {catalog : Catalog} (extension : Catalog)
    {key : ForeignKey} {position : Nat} {comparison : ParentKey}
    (located : catalog.parentLink key = .located position comparison) :
    (catalog ++ extension).parentLink key = .located position comparison := by
  unfold Catalog.parentLink at located ⊢
  cases found : catalog.findTable key.table with
  | none =>
    simp only [found] at located
    split at located <;> cases located
  | some pair =>
    rcases pair with ⟨parent, shape⟩
    rw [Catalog.findTable_append_of_some extension found]
    simp only [found] at located
    cases selected : catalog.parentKey parent shape key with
    | none => simp [selected] at located
    | some actual =>
      simp only [Catalog.parentKey_append_of_some extension selected]
      simpa only [selected] using located

/-- For any database with compatible parent schemas under a supplied mapping, appending
any catalog objects preserves the selected parent link of every old declaration. New
foreign-key declarations are outside this statement. Proof sketch: compatibility makes
each old link located, so append keeps its parent-table and parent-key searches. -/
theorem Database.ParentSchemasCompatible.selection_append {database : Database} {mapping : ForeignKeyMapping}
    (holds : database.ParentSchemasCompatible mapping) (extension : Catalog)
    (position : Nat) (table : Table) (found : database.table position = some table)
    (key : ForeignKey) (declared : key ∈ table.shape.allForeignKeys) :
    (database.catalog ++ extension).parentLink key = database.catalog.parentLink key := by
  have located : (database.catalog.parentLink key).isLocated = true := by
    rw [← (holds position table found key declared).2]
    exact (holds position table found key declared).1
  cases choice : database.catalog.parentLink key with
  | missing | mismatch => simp [choice, ParentLink.isLocated] at located
  | located parent comparison => exact Catalog.parentLink_append_of_located extension choice

end Belay.Sqlite.Model
