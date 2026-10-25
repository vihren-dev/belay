import Belay.Sqlite.Model.ForeignKeyMappingLaws
import Belay.Sqlite.Model.Resolution.PragmaResolution

set_option doc.verso true

/-! Separate preparation of the foreign-key check pragma from row validity. Compatible parent
schemas suffice for preparation, including when the child table has no rows. -/

namespace Belay.Sqlite.Model

/-- For every resolution state, the database-wide foreign-key pragma prepares as its row query
exactly when no catalog position has a mismatch. Missing parents do not count as mismatches.
This does not establish compatible parent schemas or valid row references. Proof sketch: the
resolver returns the query only when its finite list of mismatch errors is empty. -/
theorem resolvePragma_keyCheck_iff (state : ResolveState) :
    resolvePragma state (.foreignKeyCheck none) = .ok (keyCheckQuery none, state) ↔
      ∀ position < state.catalog.length, state.catalog.keyMismatch position = none := by
  have empty : (List.range state.catalog.length).filterMap state.catalog.keyMismatch = [] ↔
      ∀ position < state.catalog.length, state.catalog.keyMismatch position = none := by
    simp
  rw [← empty]
  unfold resolvePragma
  cases errors : (List.range state.catalog.length).filterMap state.catalog.keyMismatch with
  | nil => simp
  | cons first rest => cases rest <;> simp [keyCheckQuery]

/-- For every state and table name found at a position, the table-specific foreign-key pragma
prepares as its row query exactly when that position has no mismatch. Other tables impose no
condition; a missing referenced parent still permits preparation. Proof sketch: substitute the
lookup and inspect the optional prepare error. -/
theorem resolvePragma_tableKeyCheck_iff (state : ResolveState) (name : Identifier) (position : Nat)
    (shape : CatalogTable) (found : state.catalog.findTable name = some (position, shape)) :
    resolvePragma state (.foreignKeyCheck (some name)) = .ok (keyCheckQuery (some position), state) ↔
      state.catalog.keyMismatch position = none := by
  simp only [resolvePragma, found]
  cases state.catalog.keyMismatch position <;> simp [keyCheckQuery]

/-- Compatible parent schemas imply that every catalog position has no pragma mismatch,
for any supplied mapping. The converse fails when a parent is missing. Proof sketch: each
catalog child link comes from a declaration with a located selected parent; thus the pragma's
mismatch search finds nothing. -/
theorem Database.ParentSchemasCompatible.noMismatch {database : Database} {mapping : ForeignKeyMapping}
    (compatible : database.ParentSchemasCompatible mapping) (position : Nat) :
    database.catalog.keyMismatch position = none := by
  simp only [Catalog.keyMismatch, List.findSome?_eq_none_iff]
  intro link member
  obtain ⟨child, selected, shape, atShape, declared⟩ :=
    (database.catalog.mem_childLinks_iff position link).mp member
  let table : Table := { shape, rows := database.rows.getD position [] }
  have present : database.table position = some table := by simp [Database.table, atShape, table]
  obtain ⟨located, same⟩ := compatible position table present link.key declared
  have target : link.parent.isLocated = true := by rw [selected, ← same]; exact located
  cases parent : link.parent with
  | located _ _ => rfl
  | missing => rfl
  | mismatch _ => simp only [parent, ParentLink.isLocated, Bool.false_eq_true] at target

end Belay.Sqlite.Model
