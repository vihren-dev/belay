import Belay.Sqlite.Model.NormalizedFieldRows
import Belay.Sqlite.Model.QueryLaws

set_option doc.verso true

/-! Full-scan order after backfilling an appended lowercase column. The new
column changes neither rowids nor existing primary-key cells or collations. -/

namespace Belay.Sqlite.Model.NormalizedField
open Resolved

/-- Mapping commutes with stable insertion when the mapped comparison agrees
on the inserted item and every item in the list. Proof sketch: each comparison
takes the same branch, and induction identifies the remaining insertion. -/
private theorem insertStable_map {α β : Type} (predicate : α → Prop)
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

/-- Mapping commutes with the stable sort on items satisfying a predicate when
the comparisons agree there. Proof sketch: stable insertion preserves that
predicate by its permutation law, so induction transports every fold step. -/
private theorem stableSort_map {α β : Type} (predicate : α → Prop)
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

/-- For wide rows and primary-key positions inside the original columns,
appending a column and arbitrary per-row cells transports the full scan by the
same row map. Proof sketch: rowid comparisons are unchanged; WITHOUT ROWID
comparisons retain each key cell, direction and collation. Stable sort then
commutes with the map. No order of the supplied row list is assumed. -/
private theorem scanRows_append (table : Table) (column : CatalogColumn)
    (extra : Row → List Value) (wide : table.RowsWide)
    (keysInside : ∀ position ∈ table.shape.primaryKey, position < table.shape.columns.length) :
    ({ shape := { table.shape with columns := table.shape.columns ++ [column] },
       rows := table.rows.map fun row => row.appendValues (extra row) } : Table).scanRows =
      table.scanRows.map (fun row => row.appendValues (extra row)) := by
  have directions : table.shape.primaryKey.map (fun position =>
      (table.shape.primaryKeyDescending,
        ((table.shape.columns ++ [column])[position]?.map (·.collation)).getD .binary)) =
      table.shape.primaryKey.map (fun position =>
        (table.shape.primaryKeyDescending,
          (table.shape.columns[position]?.map (·.collation)).getD .binary)) := by
    apply List.map_congr_left
    intro position member
    rw [List.getElem?_append_left (keysInside position member)]
  have cells (row : Row) (rowWide : row.values.length = table.shape.columns.length) :
      table.shape.primaryKey.map (fun position =>
        (row.values ++ extra row).getD position .null) = table.keyCells row := by
    apply List.map_congr_left
    intro position member
    have inside : position < row.values.length := by rw [rowWide]; exact keysInside position member
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left inside]
  unfold Table.scanRows
  simp only
  split
  · rw [directions]
    apply stableSort_map (fun row : Row => row.values.length = table.shape.columns.length)
      _ _ _ ?_ table.rows wide
    intro first firstWide second secondWide
    simp only [Table.keyCells, Row.appendValues]
    rw [cells first firstWide, cells second secondWide]
    rfl
  · apply stableSort_map (fun row : Row => row.values.length = table.shape.columns.length)
      _ _ _ ?_ table.rows wide
    intro first _ second _
    rfl

/-- For every table with wide aliased rows, original in-range primary-key
positions and no generated columns, backfilling a newly appended plain TEXT
column with lowercase gives its original full-scan cell lists with the computed
cell appended to each. The source column must be an original column. Both
rowid and WITHOUT ROWID scans retain their order, including key direction and
collation. Proof sketch: the assignment law gives the exact stored row map;
unchanged rowids and key comparisons transport the scan, then cell projection
commutes with the map. -/
theorem sourceRows_updated_lower (context : EvalContext) (table : Table)
    (column : CatalogColumn) (source : Nat)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (inside : source < table.shape.columns.length)
    (keysInside : ∀ position ∈ table.shape.primaryKey, position < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none)
    (newPlain : column.generated = none) (text : column.affinity = .text) :
    sourceRows (LiteralData.updated context (table.appendColumns [(column, .null)])
      [(table.shape.columns.length, .scalar .lower (.cons (.column source) .nil))] none) =
      (sourceRows table).map (fun row => row ++ [mapText lowerByte (row.getD source .null)]) := by
  have result : LiteralData.updated context (table.appendColumns [(column, .null)])
      [(table.shape.columns.length, .scalar .lower (.cons (.column source) .nil))] none =
      { shape := { table.shape with columns := table.shape.columns ++ [column] },
        rows := table.rows.map fun row => row.appendValues [mapText lowerByte (row.values.getD source .null)] } := by
    exact congrArg (fun rows : List Row =>
      ({ shape := { table.shape with columns := table.shape.columns ++ [column] }, rows } : Table))
      (updated_lower_append context table column source wide aliased inside plain newPlain text)
  rw [result, sourceRows, scanRows_append table column _ wide keysInside]
  simp [sourceRows, List.map_map, Row.appendValues, Function.comp_def]

end Belay.Sqlite.Model.NormalizedField
