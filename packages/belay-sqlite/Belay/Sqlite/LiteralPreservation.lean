import Belay.Sqlite.ModelFacts

set_option doc.verso true

/-! Row and catalog lemmas for ordinary literal writes. These follow from the
executable definitions; neither native row allocation nor frame rules are axioms. -/
namespace Belay.Sqlite

/-- For every profile, catalog, database, position and old/replacement tables,
assume original {name}`Conforms`, the old table's presence, equal shapes, and
replacement {name}`Table.Valid`. Then setting the replacement preserves
conformance with that catalog. A position without a table cannot meet the
assumptions. Use this theorem when a write changes only represented rows.
The proof separates the updated position from the others. -/
theorem Conforms.replaceRows {old replacement : Table} (conforms : Conforms profile catalog database)
    (present : database position = some old) (shape : replacement.shape = old.shape)
    (valid : replacement.Valid) :
    Conforms profile catalog (database.set position replacement) := by
  refine ⟨conforms.1, ?_⟩
  intro other
  by_cases same : other = position
  · subst other
    refine ⟨?_, ?_⟩
    · simpa [Database.set, present, shape] using (conforms.2 position).1
    · intro table stored
      have equal : table = replacement := by simpa [Database.set] using stored.symm
      subst table
      exact valid
  · simpa [Database.set, same] using conforms.2 other

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

/-- For every table and value list, assume {name}`Table.Valid`, a valid newly
allocated rowid, and one supplied value per column. Then {name}`LiteralData.insertRow`
satisfies {name}`Table.Valid`. Old row checks are vacuous for an empty table;
new row bounds and width still apply. This says nothing about key constraints.
The proof makes the new rowid fresh using {name}`LiteralData.rowid_lt_next`,
then handles the old rows and the appended row separately. -/
theorem Table.Valid.insertRow (valid : table.Valid)
    (bounded : validRowid (LiteralData.nextRowid table.rows))
    (width : values.length = table.shape.columns.length) :
    (LiteralData.insertRow table values).Valid := by
  refine ⟨?_, ?_⟩
  · have fresh : LiteralData.nextRowid table.rows ∉ table.rows.map Row.rowid := by
      intro member
      obtain ⟨row, member, equal⟩ := List.mem_map.mp member
      have smaller := LiteralData.rowid_lt_next member
      omega
    simp only [LiteralData.insertRow, List.map_append, List.map_cons, List.map_nil, List.nodup_append]
    refine ⟨valid.1, by simp, ?_⟩
    intro identity member other freshMember equal
    simp only [List.mem_singleton] at freshMember
    exact fresh ((equal.trans freshMember) ▸ member)
  · intro row member
    simp only [LiteralData.insertRow, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact valid.2 row old
    · exact ⟨bounded, width⟩

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
NOT NULL checks on zipped new column/cell pairs, and a false key comparison
between every old row and the new row for every key. Then the table after
{name}`LiteralData.insertRow` satisfies the same check. With no keys the freshness
requirement is vacuous; with no old rows each key's pairwise check is vacuous.
Row width and allocation bounds are not assumed. The proof separates old and new
NOT NULL checks, then applies {name}`LiteralData.uniqueRows_append` to each key. -/
theorem LiteralData.insertRow_constraints (old : constraints keys table = true)
    (nonnull : (table.shape.columns.zip values).all (fun (column, value) =>
      !column.notNull || value != .null) = true)
    (fresh : ∀ key ∈ keys, ∀ row ∈ table.rows,
      keyEqual key row { rowid := nextRowid table.rows, values := values } = false) :
    constraints keys (insertRow table values) = true := by
  simp only [constraints, Bool.and_eq_true] at old ⊢
  constructor
  · simpa [insertRow, List.all_append, nonnull] using old.1
  · apply List.all_eq_true.mpr
    intro key member
    exact uniqueRows_append (List.all_eq_true.mp old.2 key member) (fresh key member)

/-- For every table, key position and value list, assume old
{name}`LiteralData.comparisonReady` and an integer-or-NULL value at that position
of the new row. Then the table after {name}`LiteralData.insertRow` remains
comparison-ready at the position. An empty old table still needs the column
affinity requirement. The proof retains the column test and separates old rows
from the added row. -/
theorem LiteralData.insertRow_comparison (old : comparisonReady table position = true)
    (cell : (values[position]?).any integerOrNull = true) :
    comparisonReady (insertRow table values) position = true := by
  simp only [comparisonReady, Bool.and_eq_true] at old ⊢
  refine ⟨old.1, ?_⟩
  change (table.rows ++ [(⟨nextRowid table.rows, values⟩ : Row)]).all
    (fun row => (read row position).any integerOrNull) = true
  rw [List.all_append, old.2]
  simp [read, cell]

end Belay.Sqlite
