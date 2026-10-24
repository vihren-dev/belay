import Belay.Sqlite.Model.ForeignKeyRowFrame
import Belay.Sqlite.Model.KeysUniqueDrop
import Belay.Sqlite.Model.DatabaseShapedLaws

set_option doc.verso true

/-! Foreign-key row facts after DROP: transport catalog positions while retaining the parent
comparisons and rows that surviving declarations use. -/

namespace Belay.Sqlite.Model

/-- For every database and kept position, a drop keeps the whole table at its transported
position, or the absence of a table there. Proof sketch: the catalog table definition and its
row list both remain at the new position. -/
theorem Database.table_drop_kept (database : Database) (positions : List Nat) {position : Nat}
    (kept : !positions.contains position) :
    (database.drop positions).table (keptBelow positions position) = database.table position := by
  simp only [Database.table, Database.drop, Catalog.tableAt_drop_kept _ kept]
  have rows : (keptAfterDrop positions database.rows).getD (keptBelow positions position) [] =
      database.rows.getD position [] := by
    simp only [List.getD_eq_getElem?_getD, getElem?_keptAfterDrop _ _ kept]
  change (database.catalog.tableAt position).map (fun shape =>
      ({ shape, rows := (keptAfterDrop positions database.rows).getD (keptBelow positions position) [] } : Table)) = _
  rw [rows]

/-- A drop preserves row references under the supplied transported mapping if every located
parent read by every declared key is kept. The condition covers mappings supplied by callers,
even when their targets do not name tables. Supporting indexes may be removed. Proof sketch:
each remaining child is the old table at its new position, and every mapped parent retains its
column definitions and rows. The independent row frame then applies. -/
theorem Database.RowReferencesHold.drop {database : Database} {mapping : ForeignKeyMapping}
    (holds : database.RowReferencesHold mapping) (positions : List Nat) (transported : ForeignKeyMapping)
    (mappingMoved : ∀ child table, database.table child = some table →
      ∀ key ∈ table.shape.allForeignKeys,
        transported.parent (keptBelow positions child) key = (mapping.parent child key).transport (keptBelow positions))
    (parentsKept : ∀ child table, database.table child = some table →
      ∀ key ∈ table.shape.allForeignKeys, ∀ parent comparison,
        mapping.parent child key = .located parent comparison → !positions.contains parent) :
    (database.drop positions).RowReferencesHold transported := by
  apply holds.frame (move := keptBelow positions)
  intro position table present
  obtain ⟨old, kept, moved, found⟩ := Database.table_drop_cases present
  subst position
  refine ⟨old, table, found, ⟨fun _ member => member, fun _ member => member,
    mappingMoved old table found, ?_⟩⟩
  intro key declared
  cases selected : mapping.parent old key with
  | missing => trivial
  | mismatch _ => trivial
  | located parent comparison =>
    have kept := parentsKept old table found key declared parent comparison selected
    constructor
    · exact congrArg (Option.map CatalogTable.columns) (database.catalog.tableAt_drop_kept kept)
    · exact congrArg (fun table => (table.map Table.rows).getD []) (database.table_drop_kept positions kept)

end Belay.Sqlite.Model
