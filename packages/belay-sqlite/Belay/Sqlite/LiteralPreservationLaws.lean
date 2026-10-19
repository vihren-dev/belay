import Belay.Sqlite.ModelLaws

set_option doc.verso true

/-! Row and catalog lemmas for ordinary literal writes. These follow from the
executable definitions; neither native row allocation nor frame rules are axioms. -/
namespace Belay.Sqlite

/-- For every row list and initial integer, the folded maximum is at least
the initial value and every listed rowid. With no rows the second condition
is vacuous and the first is equality. Use these bounds for row allocation.
The proof inducts on the list and applies transitivity through each maximum. -/
theorem foldRowMaximum (rows : List Row) (initial : Int) :
    initial ≤ rows.foldl (fun largest row => max largest row.rowid) initial ∧
    ∀ row ∈ rows, row.rowid ≤ rows.foldl (fun largest row => max largest row.rowid) initial := by
  induction rows generalizing initial with
  | nil => simp
  | cons first rest ih =>
    have tail := ih (max initial first.rowid)
    refine ⟨Int.le_trans (Int.le_max_left ..) tail.1, ?_⟩
    intro row member
    rcases List.mem_cons.mp member with equal | member
    · subst row
      exact Int.le_trans (Int.le_max_right ..) tail.1
    · exact tail.2 row member

/-- For every row and list containing it, its rowid is strictly below
{name}`LiteralData.nextRowid`. Membership excludes an empty list; boundedness
and table validity are not assumed. Use this to prove the allocated rowid fresh.
The proof bounds the rowid by the folded maximum, then adds one. -/
theorem LiteralData.rowid_lt_next (member : row ∈ rows) : row.rowid < nextRowid rows := by
  cases rows with
  | nil => simp at member
  | cons first rest =>
    have bounds := foldRowMaximum rest first.rowid
    have below : row.rowid ≤ rest.foldl (fun largest row => max largest row.rowid) first.rowid := by
      rcases List.mem_cons.mp member with equal | member
      · subst row; exact bounds.1
      · exact bounds.2 row member
    simp only [nextRowid]
    omega

/-- For every key, old row list and added row, assume {name}`LiteralData.uniqueRows`
on the old list and false {name}`LiteralData.keyEqual` from every old row to the
addition. Then uniqueness holds after appending that row. For no old rows, both
assumptions hold vacuously. Use this to establish a new row's key constraint.
The proof inducts on the old list and separates its head from the appended row. -/
theorem LiteralData.uniqueRows_append (unique : uniqueRows key rows = true)
    (fresh : ∀ row ∈ rows, keyEqual key row added = false) :
    uniqueRows key (rows ++ [added]) = true := by
  induction rows with
  | nil => simp [uniqueRows]
  | cons row rest ih =>
    simp only [uniqueRows, Bool.and_eq_true] at unique
    simp only [List.cons_append, uniqueRows, List.any_append, List.any_cons, List.any_nil,
      Bool.or_false, fresh row (by simp), Bool.or_false]
    rw [unique.1, ih unique.2 (fun item member => fresh item (List.mem_cons_of_mem row member))]
    rfl

/-- For every key list, table and value list, assume old {name}`LiteralData.constraints`,
NOT NULL checks on the zipped new column/cell pairs of {name}`LiteralData.newCells`,
and a false key comparison between every old row and the new row for every key. Then
the table after
{name}`LiteralData.insertRow` satisfies the same check. With no keys the freshness
requirement is vacuous; with no old rows each key's pairwise check is vacuous.
Row width and allocation bounds are not assumed. The proof separates old and new
NOT NULL checks, then applies {name}`LiteralData.uniqueRows_append` to each key. -/
theorem LiteralData.insertRow_constraints (old : constraints keys table = true)
    (nonnull : (table.shape.columns.zip (newCells table values (newRowid table values))).all (fun (column, value) =>
      !column.notNull || value != .null) = true)
    (fresh : ∀ key ∈ keys, ∀ row ∈ table.rows,
      keyEqual key row { rowid := newRowid table values, values := newCells table values (newRowid table values) } =
        false) :
    constraints keys (insertRow table values) = true := by
  simp only [constraints, Bool.and_eq_true] at old ⊢
  constructor
  · simpa [insertRow, List.all_append, nonnull] using old.1
  · apply List.all_eq_true.mpr
    intro key member
    exact uniqueRows_append (List.all_eq_true.mp old.2 key member) (fresh key member)

/-- For every column list and row: if {name}`LiteralData.storedForm` holds for every
column/cell pair of the zip, the row is {name}`Row.Stored` for the columns. Use this to
prove stored form of a concrete row by computation, or of an admitted inserted row.
Proof sketch: a position with both a column and a cell gives a pair of the zip. -/
theorem Row.Stored.of_storedForm {columns : List CatalogColumn} {row : Row}
    (all : (columns.zip row.values).all (fun (column, value) => LiteralData.storedForm column.affinity value) = true) :
    row.Stored columns := by
  intro position column value columnAt cellAt
  have pair : (columns.zip row.values)[position]? = some (column, value) := by
    simp [List.getElem?_zip_eq_some, columnAt, cellAt]
  have member := List.mem_of_getElem? pair
  have check := List.all_eq_true.mp all _ member
  simpa [LiteralData.storedForm] using check

/-- For every column list and row: if the row is {name}`Row.Stored` for the columns,
{name}`LiteralData.storedForm` holds for every column/cell pair of the zip. Proof
sketch: a pair of the zip has a position with that column and that cell. -/
theorem Row.Stored.storedForm {columns : List CatalogColumn} {row : Row} (stored : row.Stored columns) :
    (columns.zip row.values).all (fun (column, value) => LiteralData.storedForm column.affinity value) = true := by
  apply List.all_eq_true.mpr
  intro ⟨column, value⟩ member
  obtain ⟨position, pair⟩ := List.mem_iff_getElem?.mp member
  rw [List.getElem?_zip_eq_some] at pair
  simpa [LiteralData.storedForm] using stored position column value pair.1 pair.2

/-- Decide {name}`Row.Stored` by computing {name}`LiteralData.storedForm` over the zip of
columns and cells, so a concrete row's stored form can be proved with {lit}`decide`. -/
instance Row.decidableStored (columns : List CatalogColumn) (row : Row) : Decidable (row.Stored columns) :=
  decidable_of_iff _ ⟨Row.Stored.of_storedForm, Row.Stored.storedForm⟩


/-- For all integers, two integer key cells conflict ({name}`LiteralData.keyCellsEqual`)
exactly when the integers are equal: the integer keys of the model before slice 5a are a
special case of SQLite's key equality. Proof sketch: both cells rank as numbers and have
no bytes, so the comparison is that of the integers times the same nonzero factor. -/
theorem LiteralData.keyCellsEqual_integer (a b : Int) : keyCellsEqual (.integer a) (.integer b) = (a == b) := by
  simp only [keyCellsEqual, Collation.compare, Collation.key, compareValues, compareLex, compareOn, Value.rank,
    Value.scaled, Value.bytes]
  have pos : (2 : Int) ^ 1074 ≠ 0 := Int.pow_ne_zero (by decide)
  generalize (2 : Int) ^ 1074 = factor at *
  by_cases h : a = b
  · subst h; simp
  · have ne : a * factor ≠ b * factor := fun e => h (Int.eq_of_mul_eq_mul_right pos e)
    have c : compare (a * factor) (b * factor) ≠ .eq := fun e => ne (Std.LawfulEqCmp.eq_of_compare e)
    have lhs : (compare (a * factor) (b * factor) == Ordering.eq) = false := by
      cases hc : compare (a * factor) (b * factor) <;> simp_all
    simp [lhs, h]

end Belay.Sqlite
