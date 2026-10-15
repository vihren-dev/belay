import Belay.Sqlite.LiteralPreservation
import Belay.Sqlite.RowUpdate
import Belay.Sqlite.StoreValueLaws

set_option doc.verso true

/-! Row lemmas for rowid aliases (ADR 0012, amendment 4, slice 5b): the cells that INSERT
writes for a new row keep their width and stored form and make the row
{lit}`Row.Aliased`, and the rows that INSERT appends keep {lit}`Table.RowsValid`. The
distinct rowids of a write's result come from the check of {lit}`checkedWrite`, not
from the rows themselves, since an explicit alias may repeat a rowid. -/

namespace Belay.Sqlite

/-- For every table, cell list and rowid, {name}`LiteralData.newCells` keeps the number
of cells. -/
theorem LiteralData.newCells_length (table : Table) (values : List Value) (rowid : Int) :
    (newCells table values rowid).length = values.length := by
  unfold newCells
  split <;> simp

/-- For every table, cell list and rowid: if the cells are {name}`Row.Stored` for the
table's columns and the alias is {name}`LiteralData.aliasReady`, the cells of
{name}`LiteralData.newCells` are stored too. Proof sketch: the alias cell becomes an
integer, which INTEGER affinity keeps; every other cell stays. -/
theorem Row.Stored.newCells {table : Table} {values : List Value} {rowid other : Int}
    (stored : Row.Stored table.shape.columns { rowid := other, values })
    (ready : LiteralData.aliasReady table.shape = true) :
    Row.Stored table.shape.columns { rowid, values := LiteralData.newCells table values rowid } := by
  intro index column cell columnAt cellAt
  unfold LiteralData.newCells at cellAt
  split at cellAt
  · rename_i position alias
    by_cases same : index = position
    · subst same
      have integer : column.affinity = .integer := by
        simp only [LiteralData.aliasReady, alias, Option.all_some, Option.any_eq_true, beq_iff_eq] at ready
        obtain ⟨found, foundAt, affinity⟩ := ready
        rw [columnAt] at foundAt
        cases foundAt
        exact affinity
      have value : cell = .integer rowid := by
        rw [List.getElem?_set_self'] at cellAt
        cases h : values[index]? with
        | none => simp [h] at cellAt
        | some _ => simp [h] at cellAt; exact cellAt.symm
      subst value
      rw [integer]
      rfl
    · rw [List.getElem?_set_ne (Ne.symm same)] at cellAt
      exact stored index column cell columnAt cellAt
  · exact stored index column cell columnAt cellAt

/-- For every table, cell list and rowid: if the cells have one value per column and the
alias is {name}`LiteralData.aliasReady`, the row of the rowid and
{name}`LiteralData.newCells` is {name}`Row.Aliased`. Proof sketch: the alias position is
a column, so a cell, and {name}`LiteralData.newCells` sets it to the rowid. -/
theorem Row.Aliased.newCells {table : Table} {values : List Value} {rowid : Int}
    (width : values.length = table.shape.columns.length) (ready : LiteralData.aliasReady table.shape = true) :
    Row.Aliased table.shape.rowidAlias { rowid, values := LiteralData.newCells table values rowid } := by
  intro position alias
  simp only [LiteralData.aliasReady, alias, Option.all_some, Option.any_eq_true] at ready
  obtain ⟨_, foundAt, _⟩ := ready
  have inside : position < values.length := width ▸ (List.getElem?_eq_some_iff.mp foundAt).1
  simp [LiteralData.newCells, alias, List.getElem?_set_self, inside]

/-- For every table and cell list: assume {name}`Table.RowsValid`,
{name}`LiteralData.aliasReady`, a valid new rowid, one value per column and the cells in
stored form. Then {name}`LiteralData.insertRow` keeps {name}`Table.RowsValid`. -/
theorem Table.RowsValid.insertRow {table : Table} {values : List Value} (valid : table.RowsValid)
    (ready : LiteralData.aliasReady table.shape = true) (bounded : validRowid (LiteralData.newRowid table values))
    (width : values.length = table.shape.columns.length)
    (stored : Row.Stored table.shape.columns { rowid := 0, values }) :
    (LiteralData.insertRow table values).RowsValid := by
  intro row member
  simp only [LiteralData.insertRow, List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · exact valid row old
  · exact ⟨bounded, (LiteralData.newCells_length ..).trans width, stored.newCells ready,
      Row.Aliased.newCells width ready⟩

/-- For every columns, assignments, row and position that no assignment sets,
{name}`LiteralData.assign` keeps the cell at the position. -/
theorem LiteralData.assign_unassigned (columns : List CatalogColumn) (assignments : List (Nat × Resolved.Expr))
    (row : Row) (position : Nat) (unassigned : ∀ assignment ∈ assignments, assignment.1 ≠ position) :
    (assign columns assignments row).values[position]? = row.values[position]? := by
  unfold assign
  suffices ∀ (values : List Value), (assignments.foldl (fun values (position, expression) => values.set position
      (storeValue (positionAffinity columns position) (expression.eval row.values))) values)[position]? =
      values[position]? from this row.values
  induction assignments with
  | nil => intro values; rfl
  | cons assignment rest ih =>
    intro values
    obtain ⟨set, expression⟩ := assignment
    have other : set ≠ position := unassigned (set, expression) (by simp)
    simp only [List.foldl_cons]
    rw [ih (fun item member => unassigned item (List.mem_cons_of_mem _ member)) _, List.getElem?_set_ne other]

/-- For every alias and row, {name}`LiteralData.movedRowid` keeps the cells. -/
theorem LiteralData.movedRowid_values (alias : Option Nat) (row : Row) : (movedRowid alias row).values = row.values := by
  unfold movedRowid
  split <;> rfl

/-- For every row whose cells give an integer at the alias position,
{name}`LiteralData.movedRowid` makes it {name}`Row.Aliased`. -/
theorem Row.Aliased.movedRowid {position : Nat} {row : Row} {value : Int}
    (cell : row.values[position]? = some (.integer value)) :
    Row.Aliased (some position) (LiteralData.movedRowid (some position) row) := by
  intro other same
  cases same
  simp [LiteralData.movedRowid, cell]

/-- For every column list, cell list, position and value: if the cells are
{name}`Row.Stored` for the columns, setting the position to {name}`storeValue` of the
value with {name}`LiteralData.positionAffinity` keeps them stored. Proof sketch: at the
set position the cell is a stored value, which {name}`storeValue_storeValue` keeps;
every other position keeps its cell. -/
theorem Row.Stored.setStored {columns : List CatalogColumn} {rowid : Int} {values : List Value}
    (stored : Row.Stored columns { rowid, values }) (position : Nat) (value : Value) :
    Row.Stored columns
      { rowid, values := values.set position (storeValue (LiteralData.positionAffinity columns position) value) } := by
  intro index column cell columnAt cellAt
  by_cases same : index = position
  · subst same
    simp only [List.getElem?_set_self'] at cellAt
    cases h : values[index]? with
    | none => simp [h] at cellAt
    | some _ =>
      simp only [h, Functor.map, Option.map, Option.some.injEq, Function.const_apply] at cellAt
      subst cellAt
      simp [LiteralData.positionAffinity, columnAt, storeValue_storeValue]
  · rw [List.getElem?_set_ne (Ne.symm same)] at cellAt
    exact stored index column cell columnAt cellAt

/-- For every column list, assignments and row: {name}`LiteralData.assign` keeps the
rowid, the number of cells, and {name}`Row.Stored`. Proof sketch: induction on the
assignments, each a {lit}`set` of a stored value ({name}`Row.Stored.setStored`). -/
theorem LiteralData.assign_valid (columns : List CatalogColumn) (assignments : List (Nat × Resolved.Expr))
    (row : Row) (stored : row.Stored columns) :
    (assign columns assignments row).rowid = row.rowid ∧
    (assign columns assignments row).values.length = row.values.length ∧
    (assign columns assignments row).Stored columns := by
  refine ⟨rfl, ?_⟩
  unfold assign
  suffices ∀ (values : List Value), Row.Stored columns { rowid := row.rowid, values } →
      (assignments.foldl (fun values (position, expression) => values.set position
        (storeValue (positionAffinity columns position) (expression.eval row.values))) values).length = values.length ∧
      Row.Stored columns { rowid := row.rowid, values := assignments.foldl (fun values (position, expression) =>
        values.set position (storeValue (positionAffinity columns position) (expression.eval row.values))) values } from
    this row.values stored
  induction assignments with
  | nil => intro values stored; exact ⟨rfl, stored⟩
  | cons assignment rest ih =>
    intro values stored
    obtain ⟨position, expression⟩ := assignment
    have next := ih _ (Row.Stored.setStored stored position (expression.eval row.values))
    simp only [List.foldl_cons] at next ⊢
    exact ⟨next.1.trans (List.length_set ..), next.2⟩

/-- For every valid table, assignments and filter: assume {name}`LiteralData.aliasReady`,
no {name}`LiteralData.updateMismatch`, and a bounded rowid for every updated row. Then
{name}`LiteralData.updated` satisfies {name}`Table.RowsValid`. Proof sketch: an unselected
row stays; a selected row is {name}`LiteralData.assign` of a valid row with the rowid of
{name}`LiteralData.movedRowid`; its alias cell is the new integer when the assignments set
it (no mismatch), and the old rowid otherwise. -/
theorem Table.RowsValid.updated {table : Table} (valid : table.Valid) (assignments : List (Nat × Resolved.Expr))
    (filter : Option Resolved.Expr) (match_ : LiteralData.updateMismatch table assignments filter = false)
    (bounded : (LiteralData.updated table assignments filter).rows.all (fun row => LiteralData.boundedInteger row.rowid)
      = true) :
    (LiteralData.updated table assignments filter).RowsValid := by
  intro row member
  have rowBounded := List.all_eq_true.mp bounded row member
  have rowid : validRowid row.rowid := by simpa [LiteralData.boundedInteger, validRowid] using rowBounded
  simp only [LiteralData.updated, List.mem_map] at member
  obtain ⟨old, oldMember, equal⟩ := member
  subst equal
  obtain ⟨_, width, stored, aliased⟩ := valid.2 old oldMember
  split
  · rename_i chosen
    obtain ⟨_, sameLength, newStored⟩ := LiteralData.assign_valid table.shape.columns assignments old stored
    refine ⟨by simpa [chosen] using rowid, ?_, ?_, ?_⟩
    · simpa [LiteralData.movedRowid_values, sameLength, LiteralData.updated] using width
    · intro position column value columnAt cellAt
      rw [LiteralData.movedRowid_values] at cellAt
      exact newStored position column value columnAt cellAt
    · intro position alias
      have alias : table.shape.rowidAlias = some position := alias
      rw [alias]
      by_cases assigned : assignments.any (·.1 == position)
      · have cellIntegral : ∃ value, (LiteralData.assign table.shape.columns assignments old).values[position]? =
            some (.integer value) := by
          simp only [LiteralData.updateMismatch, alias, assigned, Bool.true_and, List.any_eq_false,
            Bool.and_eq_true, not_and, Bool.not_eq_true] at match_
          have cell := match_ old oldMember chosen
          revert cell
          cases (LiteralData.assign table.shape.columns assignments old).values[position]? with
          | none => simp
          | some value => cases value <;> simp
        obtain ⟨value, cell⟩ := cellIntegral
        exact Row.Aliased.movedRowid cell position rfl
      · have unassigned : ∀ assignment ∈ assignments, assignment.1 ≠ position := by
          intro assignment member same
          exact assigned (List.any_eq_true.mpr ⟨assignment, member, by simp [same]⟩)
        have cell := LiteralData.assign_unassigned table.shape.columns assignments old position unassigned
        rw [aliased position alias] at cell
        exact Row.Aliased.movedRowid cell position rfl
  · exact valid.2 old oldMember |>.elim fun rowid rest => ⟨rowid, rest⟩

end Belay.Sqlite
