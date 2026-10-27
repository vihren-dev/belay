import Belay.Sqlite.Model.InsertSelectSuccess
import Belay.Sqlite.Model.PlainInsertRows
import Belay.Sqlite.Model.DatabaseConstraints
import Belay.Sqlite.Model.RowLocalWrites
import Belay.Sqlite.Model.IntegrityCheckKeys

set_option doc.verso true

/-! Copying a table with INSERT from a query (ADR 0017, S6). A rebuild of a table copies the rows of the old
table into a new, empty table with the same columns. This module says when such a copy fits: the rows that
the old table holds are the rows that the new table receives, and the new table meets its constraints when
the old rows meet the NOT NULL columns of the new table. -/

namespace Belay.Sqlite.Model

/-- For every table shape with a rowid alias at a position and no generated column, every table of that
shape, and every list of rows that have the integer rowid in the alias cell: the rows of the table after
inserting the cells of the rows, one after the other ({name}`LiteralData.inserted`), are the old rows and the
given rows. In plain words, an INSERT whose cells carry their own rowid in the alias cell gives the same
rows. Proof sketch: induction on the rows; for one row the new rowid is the alias cell, and setting the
alias cell to that integer and computing no generated column leaves the cells. -/
theorem LiteralData.inserted_copy_rows (shape : CatalogTable) (position : Nat)
    (alias : shape.rowidAlias = some position) (plain : ∀ column ∈ shape.columns, column.generated = none) :
    ∀ (source : List Row) (target : Table), target.shape = shape →
      (∀ row ∈ source, row.values[position]? = some (.integer row.rowid)) →
      (LiteralData.inserted target (source.map Row.values)).rows = target.rows ++ source
  | [], target, _, _ => by simp [LiteralData.inserted]
  | row :: rest, target, same, aliased => by
    have cell := aliased row (List.mem_cons_self ..)
    have one : LiteralData.insertRow target row.values =
        { target with rows := target.rows ++ [row] } := by
      have rowid : LiteralData.newRowid target row.values = row.rowid := by
        simp [LiteralData.newRowid, same, alias, cell]
      have cells : LiteralData.newCells target row.values row.rowid = row.values := by
        unfold LiteralData.newCells
        rw [LiteralData.generatedCells_plain _ _ (same ▸ plain)]
        simp only [same, alias]
        obtain ⟨inRange, element⟩ := List.getElem?_eq_some_iff.mp cell
        rw [show Value.integer row.rowid = row.values[position] from element.symm]
        exact List.set_getElem_self inRange
      simp [LiteralData.insertRow, rowid, cells]
    have step : LiteralData.inserted target ((row :: rest).map Row.values) =
        LiteralData.inserted { target with rows := target.rows ++ [row] } (rest.map Row.values) := by
      simp [LiteralData.inserted, one]
    rw [step, LiteralData.inserted_copy_rows shape position alias plain rest { target with rows := target.rows ++ [row] }
      same (fun other member => aliased other (List.mem_cons_of_mem _ member))]
    simp

/-- For every empty table and list of rows that carry their rowid in the alias cell (as in
{name}`LiteralData.inserted_copy_rows`): inserting the cells of the rows gives the table of the same shape that
holds the rows. In plain words, a table that is filled with the cells of rows holds those rows. Proof sketch:
{name}`LiteralData.inserted_shape` and {name}`LiteralData.inserted_copy_rows`. -/
theorem LiteralData.inserted_copy (target : Table) (position : Nat) (source : List Row) (empty : target.rows = [])
    (alias : target.shape.rowidAlias = some position)
    (plain : ∀ column ∈ target.shape.columns, column.generated = none)
    (aliased : ∀ row ∈ source, row.values[position]? = some (.integer row.rowid)) :
    LiteralData.inserted target (source.map Row.values) = ⟨target.shape, source⟩ := by
  have shape := LiteralData.inserted_shape target (source.map Row.values)
  have rows := LiteralData.inserted_copy_rows target.shape position alias plain source target rfl aliased
  rw [empty] at rows
  cases inserted : LiteralData.inserted target (source.map Row.values) with
  | mk shape' rows' =>
    rw [inserted] at shape rows
    simp_all

/-- A pair is in the zip of two lists exactly when its two parts are at one position of the two lists. -/
private theorem mem_zip_iff_position {α β : Type} {first : List α} {second : List β} {a : α} {b : β} :
    (a, b) ∈ first.zip second ↔ ∃ i : Nat, first[i]? = some a ∧ second[i]? = some b := by
  rw [List.mem_iff_getElem?]
  simp [List.getElem?_zip_eq_some]

/-- For every key on the rowid alias cell of a table (one term, the cell at the position, and no filter) and every
list of rows that carry their rowid in that cell and do not repeat a rowid: the rows do not conflict on the key
({name}`LiteralData.uniqueRows`). In plain words, a key on the rowid alias is kept by distinct rowids. Proof
sketch: induction on the rows; two integer cells conflict only when they are equal, and the rowids differ. -/
theorem LiteralData.uniqueRows_alias (key : UniqueKey) (position : Nat)
    (terms : key.terms = [{ term := .column position }]) (filter : key.filter = none) :
    ∀ rows : List Row, (∀ row ∈ rows, row.values[position]? = some (.integer row.rowid)) →
      (rows.map Row.rowid).Nodup → LiteralData.uniqueRows key rows = true
  | [], _, _ => rfl
  | row :: rest, aliased, nodup => by
    rw [List.map_cons, List.nodup_cons] at nodup
    have apart : rest.any (LiteralData.keyEqual key row) = false := by
      rw [List.any_eq_false]
      intro other member
      have different : row.rowid ≠ other.rowid := fun same => nodup.1 (same ▸ List.mem_map_of_mem member)
      have atRow := aliased row (List.mem_cons_self ..)
      have atOther := aliased other (List.mem_cons_of_mem _ member)
      intro equal
      simp only [LiteralData.keyEqual, LiteralData.keyApplies, filter, terms, LiteralData.termValue, LiteralData.read,
        atRow, atOther, List.all_cons, List.all_nil, LiteralData.keyCellsEqual, Bool.and_true, Bool.true_and] at equal
      exact absurd (Collation.compare_integer_eq _ _ _ (by simpa using equal)) different
    simp only [LiteralData.uniqueRows, apart, Bool.not_false, Bool.true_and]
    exact LiteralData.uniqueRows_alias key position terms filter rest
      (fun other member => aliased other (List.mem_cons_of_mem _ member)) nodup.2

/-- For every empty target table with a rowid alias, without generated column, STRICT type or CHECK
constraint, whose only keys are on the alias, and every list of rows that
* carry their rowid in the alias cell, with a rowid in range and no rowid twice,
* have one cell for each column of the target, in the stored form of the column,
* and hold no NULL in a NOT NULL column of the target,

the cells of the rows fit the target ({name}`InsertFits`), when the alias of the target is an integer column.
In plain words, copying valid rows into an empty table of the same columns fits, as far as the new table
asks no more of a cell than the old one, which is the NOT NULL columns that the rows meet. Proof sketch: the
table that the insert gives holds the rows ({name}`LiteralData.inserted_copy`); each field is the Boolean form
of one premise, over the zipped columns and cells. -/
theorem InsertFits.copy (keys : List UniqueKey) (target : Table) (position : Nat) (source : List Row)
    (empty : target.rows = []) (alias : target.shape.rowidAlias = some position)
    (aliasInteger : LiteralData.aliasReady target.shape = true)
    (plain : ∀ column ∈ target.shape.columns, column.generated = none)
    (untyped : ∀ column ∈ target.shape.columns, column.strictType = none)
    (unchecked : target.shape.allChecks = [])
    (aliasKeys : ∀ key ∈ keys, key.terms = [{ term := .column position }] ∧ key.filter = none)
    (aliased : ∀ row ∈ source, row.values[position]? = some (.integer row.rowid))
    (wide : ∀ row ∈ source, row.values.length = target.shape.columns.length)
    (stored : ∀ row ∈ source, row.Stored target.shape.columns)
    (notNull : ∀ row ∈ source, ∀ (i : Nat) (column : CatalogColumn) (value : Value),
      target.shape.columns[i]? = some column → row.values[i]? = some value → column.notNull = true → value ≠ .null)
    (distinct : (source.map Row.rowid).Nodup) (inRange : ∀ row ∈ source, validRowid row.rowid) :
    InsertFits keys target (source.map Row.values) := by
  have copied := LiteralData.inserted_copy target position source empty alias plain aliased
  refine ⟨?_, aliasInteger, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro values member
    obtain ⟨row, inSource, rfl⟩ := List.mem_map.mp member
    simp [LiteralData.aliasMismatch, alias, aliased row inSource]
  · simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      Bool.and_eq_true, beq_iff_eq]
    intro row inSource
    refine ⟨wide row inSource, ?_⟩
    simp only [Prod.forall, mem_zip_iff_position]
    rintro column value ⟨i, atColumn, atValue⟩
    simpa [LiteralData.storedForm] using stored row inSource i column value atColumn atValue
  · rw [copied]
    simp only [LiteralData.notNullRows, List.all_eq_true, Prod.forall, mem_zip_iff_position, Bool.or_eq_true,
      Bool.not_eq_true', bne_iff_ne, ne_eq]
    rintro row inSource column value ⟨i, atColumn, atValue⟩
    by_cases required : column.notNull = true
    · exact Or.inr (notNull row inSource i column value atColumn atValue required)
    · exact Or.inl (by simpa using required)
  · rw [copied]
    simp only [LiteralData.typedRows, LiteralData.typesFit, List.all_eq_true, Prod.forall, mem_zip_iff_position]
    rintro row - column value ⟨i, atColumn, -⟩
    simp [untyped column (List.mem_of_getElem? atColumn)]
  · rw [copied]
    simp [LiteralData.checkedRows, LiteralData.checksHold, unchecked]
  · rw [copied]
    simp only [LiteralData.keysUnique, List.all_eq_true]
    exact fun key member => LiteralData.uniqueRows_alias key position (aliasKeys key member).1
      (aliasKeys key member).2 source aliased distinct
  · rw [copied]
    simpa [LiteralData.rowidsDistinct] using distinct
  · rw [copied]
    simp only [List.all_eq_true, LiteralData.boundedInteger, decide_eq_true_eq]
    exact inRange

end Belay.Sqlite.Model
