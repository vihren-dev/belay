import Belay.Sqlite.Model.QueryLaws

set_option doc.verso true

/-! The full scan of a table whose rows are mapped by a function (ADR 0017, S6). A migration that
rewrites each row of a table, for example by appending a derived cell, keeps the scan order when the
rewrite keeps each rowid and each primary-key cell. Then the scan of the new table is the scan of
the old table with the same rewrite. The stable sort that gives the scan order commutes with the map
when the comparison on the mapped items agrees with the comparison on the old items. -/

namespace Belay.Sqlite.Model
open Resolved

/-- For every map, comparisons and predicate: if the comparison {lit}`after` of the mapped items equals
the comparison {lit}`before` of the old items for all items with the predicate, then inserting a mapped
item that has the predicate into a mapped list of items with the predicate is the mapped insertion
({name}`insertStable`). In plain words, mapping commutes with stable insertion when the comparisons
agree. Proof sketch: induction on the list; each comparison takes the same branch. -/
theorem insertStable_map {α β : Type} (predicate : α → Prop)
    (map : α → β) (before : α → α → Bool) (after : β → β → Bool)
    (same : ∀ a, predicate a → ∀ b, predicate b → after (map a) (map b) = before a b)
    (item : α) (itemOk : predicate item) (items : List α)
    (itemsOk : ∀ entry ∈ items, predicate entry) :
    insertStable after (map item) (items.map map) = (insertStable before item items).map map := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, insertStable]
    rw [same head (itemsOk head (by simp)) item itemOk]
    split
    · simp only [List.map_cons]
      rw [ih (fun entry member => itemsOk entry (by simp [member]))]
    · rfl

/-- For every map, comparisons and predicate: if the comparison of the mapped items equals the comparison
of the old items for all items with the predicate, then the stable sort ({name}`stableSort`) of the mapped
list of items with the predicate is the mapped stable sort. In plain words, sorting and mapping commute
when the map keeps the order. No order of the supplied list is assumed. Proof sketch: stable insertion keeps
the predicate by its permutation law ({name}`insertStable_perm`), so induction on the fold transports every
step by {name}`insertStable_map`. -/
theorem stableSort_map {α β : Type} (predicate : α → Prop)
    (map : α → β) (before : α → α → Bool) (after : β → β → Bool)
    (same : ∀ a, predicate a → ∀ b, predicate b → after (map a) (map b) = before a b)
    (items : List α) (itemsOk : ∀ item ∈ items, predicate item) :
    stableSort after (items.map map) = (stableSort before items).map map := by
  have fold : ∀ (remaining sorted : List α),
      (∀ item ∈ remaining, predicate item) → (∀ item ∈ sorted, predicate item) →
      (remaining.map map).foldl (fun rows row => insertStable after row rows) (sorted.map map) =
        (remaining.foldl (fun rows row => insertStable before row rows) sorted).map map := by
    intro remaining
    induction remaining with
    | nil => intro sorted _ _; rfl
    | cons head tail ih =>
      intro sorted remainingOk sortedOk
      simp only [List.map_cons, List.foldl_cons]
      rw [insertStable_map predicate map before after same head (remainingOk head (by simp)) sorted sortedOk]
      apply ih _ (fun item member => remainingOk item (by simp [member]))
      intro item member
      rcases List.mem_cons.mp ((insertStable_perm before head sorted).mem_iff.mp member) with equal | old
      · subst item; exact remainingOk head (by simp)
      · exact sortedOk item old
  exact fold items [] itemsOk (by simp)

/-- For every table, shape and row map: if the shape has the same {lit}`WITHOUT ROWID` mode, primary key
and key direction as the table; the map keeps the rowid of each row; the key columns of the shape have the
collations of the key columns of the table; and the map keeps each primary-key cell of each row, then the
full scan ({name}`Table.scanRows`) of the table with the shape and the mapped rows is the scan of the table
with the map applied. In plain words, a rewrite that keeps rowids and key cells keeps the scan order, for a
rowid table and for a {lit}`WITHOUT ROWID` table, whatever the order of the stored rows. Proof sketch: the
scan is a stable sort; the comparison of two mapped rows is the comparison of the old rows because it reads
only the rowid, or the key cells with the directions and collations, and {name}`stableSort_map` commutes the
sort with the map. -/
theorem Table.scanRows_map (table : Table) (shape : CatalogTable) (transform : Row → Row)
    (mode : shape.withoutRowid = table.shape.withoutRowid)
    (key : shape.primaryKey = table.shape.primaryKey)
    (direction : shape.primaryKeyDescending = table.shape.primaryKeyDescending)
    (collations : ∀ position ∈ table.shape.primaryKey,
      shape.columns[position]?.map (·.collation) = table.shape.columns[position]?.map (·.collation))
    (rowids : ∀ row ∈ table.rows, (transform row).rowid = row.rowid)
    (cells : ∀ row ∈ table.rows, ∀ position ∈ table.shape.primaryKey,
      (transform row).values.getD position .null = row.values.getD position .null) :
    ({ shape, rows := table.rows.map transform } : Table).scanRows = table.scanRows.map transform := by
  have directions : shape.primaryKey.map (fun position =>
      (shape.primaryKeyDescending, (shape.columns[position]?.map (·.collation)).getD .binary)) =
      table.shape.primaryKey.map (fun position =>
        (table.shape.primaryKeyDescending, (table.shape.columns[position]?.map (·.collation)).getD .binary)) := by
    rw [key, direction]
    apply List.map_congr_left
    intro position member
    rw [collations position member]
  unfold Table.scanRows
  simp only [mode]
  split
  · rw [directions]
    apply stableSort_map (fun row : Row => row ∈ table.rows) _ _ _ ?_ table.rows (fun _ member => member)
    intro first firstMember second secondMember
    have keyCells (row : Row) (member : row ∈ table.rows) :
        ({ shape, rows := table.rows.map transform } : Table).keyCells (transform row) = table.keyCells row := by
      simp only [Table.keyCells, key]
      exact List.map_congr_left fun position inKey => cells row member position inKey
    rw [keyCells first firstMember, keyCells second secondMember]
  · apply stableSort_map (fun row : Row => row ∈ table.rows) _ _ _ ?_ table.rows (fun _ member => member)
    intro first firstMember second secondMember
    rw [rowids first firstMember, rowids second secondMember]

/-- For every table, shape and row map under the premises of {name}`Table.scanRows_map`, the source rows
of the table with the shape and the mapped rows are the cells of the mapped scan of the table. Proof
sketch: {name}`Table.scanRows_map`, then the definition of {name}`sourceRows`. -/
theorem sourceRows_map (table : Table) (shape : CatalogTable) (transform : Row → Row)
    (mode : shape.withoutRowid = table.shape.withoutRowid)
    (key : shape.primaryKey = table.shape.primaryKey)
    (direction : shape.primaryKeyDescending = table.shape.primaryKeyDescending)
    (collations : ∀ position ∈ table.shape.primaryKey,
      shape.columns[position]?.map (·.collation) = table.shape.columns[position]?.map (·.collation))
    (rowids : ∀ row ∈ table.rows, (transform row).rowid = row.rowid)
    (cells : ∀ row ∈ table.rows, ∀ position ∈ table.shape.primaryKey,
      (transform row).values.getD position .null = row.values.getD position .null) :
    sourceRows ({ shape, rows := table.rows.map transform } : Table) =
      table.scanRows.map fun row => (transform row).values := by
  rw [sourceRows, Table.scanRows_map table shape transform mode key direction collations rowids cells,
    List.map_map]
  rfl

end Belay.Sqlite.Model
