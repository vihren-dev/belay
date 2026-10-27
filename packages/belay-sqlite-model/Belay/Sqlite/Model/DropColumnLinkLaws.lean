import Belay.Sqlite.Model.ForeignKeyFacts
import Belay.Sqlite.Model.Resolution.ColumnDropParentChildren

set_option doc.verso true

/-! Whether a child row has its parent when the child columns of the key move (ADR 0019, D4). A drop of a column
of the child table moves the child columns of its foreign keys and removes a cell from each row of the child.
A key that does not name the column finds the same parent rows by the same cells, so the row has its parent
exactly when it had before. -/

namespace Belay.Sqlite.Model

/-- For every parent table, pairs, values, row and function: the lookup of a parent row by the pairs with moved
child positions is the lookup by the pairs. Proof sketch: the lookup reads the parent column of each pair only,
not the child position. -/
theorem indexHolds_mapChildren (parent : CatalogTable) (pairs : List (Nat × Nat)) (values : List Value)
    (row : Row) (move : Nat → Nat) :
    indexHolds parent (pairs.map fun pair => (move pair.1, pair.2)) values row = indexHolds parent pairs values row := by
  unfold indexHolds
  rw [List.zip_map_left, List.all_map]
  rfl

/-- For every links, parent key, function and two value lists: if the cells at the moved child columns of one
list are the cells at the child columns of the other, the values that the moved parent key selects are the values
that the parent key selects. Proof sketch: each selected position is a column of the key
({name}`Catalog.parentLink_children`) and moves to the position of the same cell. -/
theorem childValues_mapChildren {link moved : ForeignKeyLink} {move : Nat → Nat} {found : ParentKey}
    (columns : moved.key.columns = link.key.columns.map move)
    (inside : ∀ child ∈ childPositions link found, child ∈ link.key.columns) {old new : List Value}
    (cells : ∀ child ∈ link.key.columns, new.getD (move child) .null = old.getD child .null) :
    childValues moved (found.mapChildren move) new = childValues link found old := by
  unfold childValues
  cases found with
  | rowid =>
    simp only [childPositions, ParentKey.mapChildren, columns, ← List.map_take, List.map_map] at inside ⊢
    apply List.map_congr_left
    intro child member
    exact cells child (inside child member)
  | columns pairs =>
    simp only [childPositions, ParentKey.mapChildren, List.map_map] at inside ⊢
    apply List.map_congr_left
    intro pair member
    exact cells pair.1 (inside pair.1 (List.mem_map.mpr ⟨pair, member, rfl⟩))

/-- For every parent table, key, links, values, rows and function: the lookup of a parent row for the moved key and
the moved values is the lookup for the key and the values, when the values that the keys select are the same.
Proof sketch: the lookup reads the child values it selects and, for a key of columns, the parent column of each
pair ({name}`indexHolds_mapChildren`). -/
theorem parentFound_mapChildren (parent : CatalogTable) (found : ParentKey) (link moved : ForeignKeyLink)
    (move : Nat → Nat) (old new : List Value) (rows : List Row)
    (same : childValues moved (found.mapChildren move) new = childValues link found old) :
    parentFound parent (found.mapChildren move) moved new rows none = parentFound parent found link old rows none := by
  unfold parentFound
  simp only [same]
  cases found with
  | rowid => rfl
  | columns pairs =>
    simp only [ParentKey.mapChildren, Option.any_none, Bool.false_or]
    congr 1
    funext row
    exact indexHolds_mapChildren parent pairs _ row move

/-- For every databases, links and rows: if the child columns of the second link are those of the first, moved, the
second link finds the first link's parent with moved child positions, the cells of the second row at the moved
columns are the cells of the first row, and every parent that the first link locates has the same table and the same
rows in both databases, then the second row satisfies the second link exactly when the first row satisfies the first.
Proof sketch: the NULL test and the parent lookup read the same values ({name}`childValues_mapChildren`,
{name}`parentFound_mapChildren`) in the same parent. -/
theorem ForeignKeyLink.satisfied_mapChildren {old new : Database} {link moved : ForeignKeyLink} {oldRow newRow : Row}
    {move : Nat → Nat} (columns : moved.key.columns = link.key.columns.map move)
    (parent : moved.parent = link.parent.mapChildren move)
    (cells : ∀ child ∈ link.key.columns, newRow.values.getD (move child) .null = oldRow.values.getD child .null)
    (inside : ∀ place found, link.parent = .located place found → ∀ child ∈ childPositions link found, child ∈ link.key.columns)
    (same_parent : ∀ place found, link.parent = .located place found →
      new.catalog.tableAt place = old.catalog.tableAt place ∧ new.rowsAt place = old.rowsAt place) :
    moved.satisfied new newRow = link.satisfied old oldRow := by
  unfold ForeignKeyLink.satisfied ForeignKeyLink.hasNull
  rw [parent]
  cases located : link.parent with
  | located place found =>
    have values := childValues_mapChildren (found := found) columns (inside place found located) cells
    simp only [ParentLink.mapChildren, values]
    congr 1
    obtain ⟨sameTable, sameRows⟩ := same_parent place found located
    rw [sameTable, sameRows]
    cases old.catalog.tableAt place with
    | none => rfl
    | some shape => exact parentFound_mapChildren shape found link moved move _ _ _ values
  | mismatch place | missing =>
    all_goals
      simp only [ParentLink.mapChildren, columns, List.any_map]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor <;> rintro ⟨child, member, held⟩ <;> refine ⟨child, member, ?_⟩ <;>
        have cell := cells child member <;> rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at cell <;>
        simpa [cell] using held

end Belay.Sqlite.Model
