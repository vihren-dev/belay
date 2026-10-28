import Belay.Sqlite.Model.Resolution.ColumnDropCatalogLaws

set_option doc.verso true

/-! The unique keys of the tables after ALTER TABLE DROP COLUMN (ADR 0019, D4): the keys of the table that
lost the column are the keys before, with the positions of their terms changed ({lit}`UniqueKey.dropColumn`),
and the keys of every other table are as they were. -/

namespace Belay.Sqlite.Model

/-- For every column and index: the column after the drop of another column has the collation that it had.
Proof sketch: the drop changes only the CHECK constraints, the generated expression and the foreign keys. -/
@[simp] theorem CatalogColumn.collation_dropColumn (index : Nat) (column : CatalogColumn) :
    (column.dropColumn index).collation = column.collation := rfl

/-- For every columns, index, position other than the index and column map: the column at the image of the
position in the columns without the column at the index, mapped, is the column at the position, mapped. Proof
sketch: {lit}`List.getElem?_eraseIdx` and a case split on the position against the index. -/
theorem dropColumn_getElem? {α β : Type} (items : List α) (index position : Nat) (map : α → β)
    (other : position ≠ index) :
    ((items.eraseIdx index).map map)[dropPosition index position]? = items[position]?.map map := by
  by_cases before : position < index
  · simp [dropPosition, before, List.getElem?_eraseIdx]
  · simp only [dropPosition, before, ↓reduceIte, List.getElem?_map, List.getElem?_eraseIdx]
    simp only [show ¬(position - 1 < index) by omega, ↓reduceIte, Nat.sub_add_cancel (show 1 ≤ position by omega)]

/-- For every columns, index and positions that do not name the index: the key of the positions of the
columns without the column at the index, with the positions changed, is the key of the positions of the
columns with its terms changed ({name}`UniqueKey.dropColumn`). Proof sketch: each term reads the collation of
the column at its position, which {name}`dropColumn_getElem?` finds in both. -/
theorem UniqueKey.ofColumns_dropColumn (columns : List CatalogColumn) (index : Nat) (positions : List Nat)
    (other : ∀ position ∈ positions, position ≠ index) :
    UniqueKey.ofColumns ((columns.eraseIdx index).map (·.dropColumn index)) (positions.map (dropPosition index)) =
      (UniqueKey.ofColumns columns positions).dropColumn index := by
  simp only [UniqueKey.ofColumns, UniqueKey.dropColumn, List.map_map, Option.map_none]
  congr 1
  apply List.map_congr_left
  intro position member
  simp only [Function.comp, KeyTerm.dropColumn, IndexKey.dropColumn]
  rw [dropColumn_getElem? columns index position (fun column => column.dropColumn index) (other position member)]
  cases columns[position]? <;> rfl

/-- For every list, indexed map, tests and function: if each mapped item gives what the item gives, mapped, the
filtered list of the mapped list is the filtered list, mapped. Proof sketch: induction over the list, with the
shifted map for the tail ({lit}`List.mapIdx_cons`). -/
theorem List.filterMap_mapIdx_eq_map {α β γ : Type} (items : List α) (move : Nat → α → α) (pick : α → Option β)
    (pickMoved : α → Option γ) (transform : β → γ)
    (same : ∀ slot item, pickMoved (move slot item) = (pick item).map transform) :
    (items.mapIdx move).filterMap pickMoved = (items.filterMap pick).map transform := by
  induction items generalizing move with
  | nil => simp
  | cons item rest ih =>
    have tail := ih (fun slot => move (slot + 1)) (fun slot other => same (slot + 1) other)
    rw [List.mapIdx_cons, List.filterMap_cons, List.filterMap_cons, same 0 item]
    cases pick item <;> simp [tail]

/-- For every table that can lose the column at the index: the keys of its primary key and UNIQUE constraints
after the drop are those before it with their positions changed. Proof sketch: the positions of the keys after
the drop are the positions before it, mapped; none of them names the column, so
{name}`UniqueKey.ofColumns_dropColumn` applies to each. -/
theorem CatalogTable.declaredKeys_dropColumnAt {table : CatalogTable} {index : Nat} (clean : table.DropsCleanly index) :
    ((if (table.dropColumnAt index).primaryKey.isEmpty then [] else [(table.dropColumnAt index).primaryKey]) ++
        (table.dropColumnAt index).uniqueKeys).map (UniqueKey.ofColumns (table.dropColumnAt index).columns) =
      (((if table.primaryKey.isEmpty then [] else [table.primaryKey]) ++ table.uniqueKeys).map
        (UniqueKey.ofColumns table.columns)).map (UniqueKey.dropColumn index) := by
  have positions : (if (table.dropColumnAt index).primaryKey.isEmpty then [] else [(table.dropColumnAt index).primaryKey]) ++
      (table.dropColumnAt index).uniqueKeys =
      ((if table.primaryKey.isEmpty then [] else [table.primaryKey]) ++ table.uniqueKeys).map (·.map (dropPosition index)) := by
    by_cases empty : table.primaryKey.isEmpty
    · simp [CatalogTable.dropColumnAt, empty]
    · simp [CatalogTable.dropColumnAt, empty]
  rw [positions, List.map_map, List.map_map]
  apply List.map_congr_left
  intro keyPositions member
  simp only [Function.comp]
  have other : ∀ p ∈ keyPositions, p ≠ index := by
    rcases List.mem_append.mp member with primary | keys
    · by_cases empty : table.primaryKey.isEmpty
      · simp [empty] at primary
      · simp only [empty, Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at primary
        subst primary
        exact clean.primary
    · exact clean.keys keyPositions keys
  exact UniqueKey.ofColumns_dropColumn table.columns index keyPositions other

/-- For every catalog, position, index and table that can lose the column: the unique keys of the table after the
drop are the unique keys before it with their positions changed ({name}`UniqueKey.dropColumn`). Proof sketch: the
declared keys are mapped ({name}`CatalogTable.declaredKeys_dropColumnAt`), and the unique indexes on the table
are mapped one by one ({name}`List.filterMap_mapIdx_eq_map`). -/
theorem Catalog.uniqueKeys_dropColumn_same (catalog : Catalog) {position index : Nat} {table : CatalogTable}
    (clean : table.DropsCleanly index) :
    (catalog.dropColumn position index).uniqueKeys position (table.dropColumnAt index) =
      (catalog.uniqueKeys position table).map (UniqueKey.dropColumn index) := by
  unfold Catalog.uniqueKeys Catalog.dropColumn
  rw [CatalogTable.declaredKeys_dropColumnAt clean]
  conv => rhs; rw [List.map_append]
  congr 1
  apply List.filterMap_mapIdx_eq_map
  intro slot object
  rcases object with ⟨name, entry⟩
  cases entry with
  | table _ => by_cases at_position : slot = position <;> simp [CatalogObject.dropColumn, at_position]
  | index definition =>
    by_cases onTable : definition.table = position
    · simp [CatalogObject.dropColumn, onTable, CatalogIndex.dropColumn]
      split <;> simp [CatalogIndex.uniqueKey, UniqueKey.dropColumn]
    · simp [CatalogObject.dropColumn, onTable, CatalogIndex.dropColumn]
  | view _ => simp [CatalogObject.dropColumn]
  | trigger _ => simp [CatalogObject.dropColumn]

/-- For every catalog, two different positions, index and table: the unique keys of the table at the other position
after the drop are those before it. Proof sketch: the declared keys come from the table, and an index of the table
at the other position is not changed ({name}`CatalogIndex.dropColumn`). -/
theorem Catalog.uniqueKeys_dropColumn_other (catalog : Catalog) {position other : Nat} (index : Nat)
    (table : CatalogTable) (different : other ≠ position) :
    (catalog.dropColumn position index).uniqueKeys other table = catalog.uniqueKeys other table := by
  unfold Catalog.uniqueKeys Catalog.dropColumn
  congr 1
  have := List.filterMap_mapIdx_eq_map catalog (CatalogObject.dropColumn position index)
    (fun object => match object.entry with
      | .index definition => if (definition.table == other && definition.unique) = true then some definition.uniqueKey else none
      | .table _ | .view _ | .trigger _ => none)
    (fun object => match object.entry with
      | .index definition => if (definition.table == other && definition.unique) = true then some definition.uniqueKey else none
      | .table _ | .view _ | .trigger _ => none) id ?_
  · rw [List.map_id] at this
    exact this
  · intro slot object
    rcases object with ⟨name, entry⟩
    cases entry with
    | table _ => by_cases at_position : slot = position <;> simp [CatalogObject.dropColumn, at_position]
    | index definition =>
      by_cases onTable : definition.table = position
      · simp [CatalogObject.dropColumn, CatalogIndex.dropColumn, onTable, Ne.symm different]
      · simp [CatalogObject.dropColumn, onTable, CatalogIndex.dropColumn]
    | view _ => simp [CatalogObject.dropColumn]
    | trigger _ => simp [CatalogObject.dropColumn]

end Belay.Sqlite.Model
