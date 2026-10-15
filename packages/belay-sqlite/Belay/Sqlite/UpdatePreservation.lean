import Belay.Sqlite.AliasPreservation
import Belay.Sqlite.StoreValueLaws

set_option doc.verso true

/-! Row lemmas for UPDATE (ADR 0012, amendment 1 and amendment 4, slice 5b): an assigned
row keeps its width and the stored form of its cells, a cell that no assignment sets
stays, and the rowid of {lit}`LiteralData.movedRowid` makes a row with an integer alias
cell {lit}`Row.Aliased`, so the rows of UPDATE keep {lit}`Table.RowsValid`. -/

namespace Belay.Sqlite

/-- For every columns, assignments, row and position that no assignment sets,
{name}`LiteralData.assign` keeps the cell at the position. Proof sketch: induction on the
assignments; each sets another position, which keeps the cell. -/
theorem LiteralData.assign_unassigned (columns : List CatalogColumn) (assignments : List (Nat × Resolved.Expr))
    (row : Row) (position : Nat) (unassigned : ∀ assignment ∈ assignments, assignment.1 ≠ position) :
    (assign columns assignments row).values[position]? = row.values[position]? := by
  unfold assign assignFrom
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

/-- For every alias and row, {name}`LiteralData.movedRowid` keeps the cells. Proof
sketch: each branch changes at most the rowid. -/
theorem LiteralData.movedRowid_values (alias : Option Nat) (row : Row) : (movedRowid alias row).values = row.values := by
  unfold movedRowid
  split <;> rfl

/-- For every row whose cells give an integer at the alias position,
{name}`LiteralData.movedRowid` makes it {name}`Row.Aliased`. Proof sketch: the rowid
becomes that integer, and the cells stay. -/
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

/-- For every column list, assignments, context and row: {name}`LiteralData.assignFrom`
keeps the rowid, the number of cells, and {name}`Row.Stored`. Proof sketch: induction on
the assignments, each a {lit}`set` of a stored value ({name}`Row.Stored.setStored`). -/
theorem LiteralData.assignFrom_valid (columns : List CatalogColumn) (assignments : List (Nat × Resolved.Expr))
    (context : List Value) (row : Row) (stored : row.Stored columns) :
    (assignFrom columns assignments context row).rowid = row.rowid ∧
    (assignFrom columns assignments context row).values.length = row.values.length ∧
    (assignFrom columns assignments context row).Stored columns := by
  refine ⟨rfl, ?_⟩
  unfold assignFrom
  suffices ∀ (values : List Value), Row.Stored columns { rowid := row.rowid, values } →
      (assignments.foldl (fun values (position, expression) => values.set position
        (storeValue (positionAffinity columns position) (expression.eval context))) values).length = values.length ∧
      Row.Stored columns { rowid := row.rowid, values := assignments.foldl (fun values (position, expression) =>
        values.set position (storeValue (positionAffinity columns position) (expression.eval context))) values } from
    this row.values stored
  induction assignments with
  | nil => intro values stored; exact ⟨rfl, stored⟩
  | cons assignment rest ih =>
    intro values stored
    obtain ⟨position, expression⟩ := assignment
    have next := ih _ (Row.Stored.setStored stored position (expression.eval context))
    simp only [List.foldl_cons] at next ⊢
    exact ⟨next.1.trans (List.length_set ..), next.2⟩

/-- For every column list, assignments and row: {name}`LiteralData.assign` keeps the
rowid, the number of cells, and {name}`Row.Stored`. Proof sketch: the case of
{name}`LiteralData.assignFrom_valid` with the row as the context. -/
theorem LiteralData.assign_valid (columns : List CatalogColumn) (assignments : List (Nat × Resolved.Expr))
    (row : Row) (stored : row.Stored columns) :
    (assign columns assignments row).rowid = row.rowid ∧
    (assign columns assignments row).values.length = row.values.length ∧
    (assign columns assignments row).Stored columns :=
  assignFrom_valid columns assignments row.values row stored

/-- For every valid table, assignments and filter: assume no
{name}`LiteralData.updateMismatch` and a bounded rowid for every updated row. Then
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
