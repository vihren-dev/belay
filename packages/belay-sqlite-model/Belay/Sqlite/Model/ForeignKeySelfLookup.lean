import Belay.Sqlite.Model.ComparisonLaws
import Belay.Sqlite.Model.ForeignKeyParentUnique

set_option doc.verso true

/-! Conditions connecting the self-parent shortcut to ordinary parent lookup. -/

namespace Belay.Sqlite.Model

/-- For every pair of conflicting BINARY key cells, the cells conflict under every
built-in collation. Proof sketch: keep non-NULLness and apply
{name}`Collation.compare_eq_of_binary`. -/
theorem LiteralData.keyCellsEqual_of_binary {first second : Value}
    (equal : keyCellsEqual first second = true) (collation : Collation) :
    keyCellsEqual first second collation = true := by
  simp only [keyCellsEqual, Bool.and_eq_true, beq_iff_eq] at equal ⊢
  exact ⟨equal.1, Collation.compare_eq_of_binary equal.2 collation⟩

/-- For this link, parent definition and key, every row stored under that definition
which the self-parent shortcut accepts is also found by the ordinary singleton lookup.
Rows rejected by the shortcut impose no requirement. This compares two ways of reading
the same future row; it does not assert a parent exists in any database. -/
def ForeignKeyLink.SelfLookupSound (link : ForeignKeyLink) (parent : CatalogTable) (key : ParentKey) : Prop :=
  ∀ row, row.Stored parent.columns → parentFound parent key link row.values [] (some row) = true →
    parentFound parent key link row.values [row] none = true

/-- For every link and parent definition, the self-parent shortcut for a rowid key
implies the ordinary lookup in that row. Proof sketch: both compare the same rowid. -/
theorem ForeignKeyLink.selfLookupSound_rowid (link : ForeignKeyLink) (parent : CatalogTable) :
    link.SelfLookupSound parent .rowid := by
  intro row _ found
  simpa only [parentFound, List.any_nil, List.any_cons, Bool.or_false, Option.any_some,
    Option.any_none, Bool.false_or] using found

/-- For every column mapping, the self-parent shortcut is sound if, for every stored
row and selected pair, the parent column exists and its index affinity leaves the child
cell unchanged. Empty mappings impose no per-column premise. Proof sketch: reverse each
BINARY equality, extend it to the parent collation, and remove the stated affinity conversion. -/
theorem ForeignKeyLink.selfLookupSound_columns (link : ForeignKeyLink) (parent : CatalogTable)
    (pairs : List (Nat × Nat))
    (normalized : ∀ (row : Row), row.Stored parent.columns → ∀ pair ∈ pairs,
      ∃ column, parent.columns[pair.2]? = some column ∧
        Value.store (indexAffinity column) (row.values.getD pair.1 .null) = row.values.getD pair.1 .null) :
    link.SelfLookupSound parent (.columns pairs) := by
  intro row stored self
  simp only [parentFound, Option.any_some, List.any_nil, Bool.or_false] at self
  simp only [childValues, childPositions, List.map_map, ← List.map_prod_left_eq_zip, List.all_map,
    List.all_eq_true] at self
  simp only [parentFound, Option.any_none, Bool.false_or, List.any_cons, List.any_nil, Bool.or_false]
  rw [indexHolds_childValues, List.all_eq_true]
  intro pair member
  obtain ⟨column, present, kept⟩ := normalized row stored pair member
  simp only [present, kept]
  exact LiteralData.keyCellsEqual_of_binary (LiteralData.keyCellsEqual_symm (self pair member)) _

/-- For every mapping whose selected parent columns exist and have BLOB affinity,
the self-parent shortcut is sound for every stored row, under any built-in collation.
Proof sketch: BLOB index affinity leaves every selected child value unchanged. -/
theorem ForeignKeyLink.selfLookupSound_blob (link : ForeignKeyLink) (parent : CatalogTable)
    (pairs : List (Nat × Nat))
    (columns : ∀ pair ∈ pairs, ∃ column, parent.columns[pair.2]? = some column ∧ column.affinity = .blob) :
    link.SelfLookupSound parent (.columns pairs) := by
  apply link.selfLookupSound_columns parent pairs
  intro row _ pair member
  obtain ⟨column, present, affinity⟩ := columns pair member
  exact ⟨column, present, by simp [indexAffinity, affinity, numericAffinity, Value.store]⟩

/-- For every mapping whose child and parent columns exist, if each parent index
affinity equals its child column affinity, the self-parent shortcut is sound for every
stored row. For example, this covers TEXT-to-TEXT and NUMERIC-to-NUMERIC mappings.
Proof sketch: the row storedness law removes each index affinity conversion. -/
theorem ForeignKeyLink.selfLookupSound_stored (link : ForeignKeyLink) (parent : CatalogTable)
    (pairs : List (Nat × Nat))
    (columns : ∀ pair ∈ pairs, ∃ childColumn parentColumn,
      parent.columns[pair.1]? = some childColumn ∧ parent.columns[pair.2]? = some parentColumn ∧
        indexAffinity parentColumn = childColumn.affinity) :
    link.SelfLookupSound parent (.columns pairs) := by
  apply link.selfLookupSound_columns parent pairs
  intro row stored pair member
  obtain ⟨childColumn, parentColumn, childAt, parentAt, affinity⟩ := columns pair member
  exact ⟨parentColumn, parentAt, by rw [affinity]; exact stored.getD childAt⟩

/-- For every key, child values, stored rows and proposed self row, lookup with that
self row is the disjunction of the self shortcut and ordinary lookup in the stored rows.
Proof sketch: split the key and the rowid conversion cases. -/
theorem parentFound_split_self (parent : CatalogTable) (key : ParentKey) (link : ForeignKeyLink)
    (values : List Value) (rows : List Row) (row : Row) :
    parentFound parent key link values rows (some row) =
      (parentFound parent key link values [] (some row) || parentFound parent key link values rows none) := by
  cases key with
  | columns pairs => simp [parentFound]
  | rowid =>
    simp only [parentFound]
    split <;> simp

end Belay.Sqlite.Model
