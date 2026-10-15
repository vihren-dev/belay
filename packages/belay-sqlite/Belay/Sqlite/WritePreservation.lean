import Belay.Sqlite.SqlExecution
import Belay.Sqlite.LiteralPreservation
import Belay.Sqlite.StoreValueLaws

set_option doc.verso true

/-! Preservation of {lit}`Conforms` by INSERT and UPDATE (ADR 0012, amendment 1,
"Proofs"): every row that a write produces has a valid rowid, one cell per column and
every cell in stored form. DELETE is in {lit}`DeletePreservation`. Schema statements keep {lit}`Conforms` by
{lit}`Conforms.appendAt` and {lit}`Conforms.set`. -/

namespace Belay.Sqlite

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

/-- For every valid table, assignments and filter, {name}`LiteralData.updated` is valid:
UPDATE keeps rowids, widths and the stored form of every cell. Proof sketch: rows are
mapped one to one; a selected row is {name}`LiteralData.assign` of a valid row, which
{name}`LiteralData.assign_valid` covers. -/
theorem Table.Valid.updated {table : Table} (valid : table.Valid) (assignments : List (Nat × Resolved.Expr))
    (filter : Option Resolved.Expr) : (LiteralData.updated table assignments filter).Valid := by
  have rowids : (LiteralData.updated table assignments filter).rows.map Row.rowid = table.rows.map Row.rowid := by
    simp only [LiteralData.updated, List.map_map]
    apply List.map_congr_left
    intro row _
    simp only [Function.comp_def]
    split <;> rfl
  refine ⟨rowids ▸ valid.1, ?_⟩
  intro row member
  simp only [LiteralData.updated, List.mem_map] at member
  obtain ⟨old, oldMember, equal⟩ := member
  subst equal
  obtain ⟨rowid, width, stored⟩ := valid.2 old oldMember
  split
  · obtain ⟨sameRowid, sameLength, newStored⟩ := LiteralData.assign_valid table.shape.columns assignments old stored
    exact ⟨sameRowid ▸ rowid, sameLength ▸ width, newStored⟩
  · exact ⟨rowid, width, stored⟩

/-- For every table and value rows, every row of the table is a row of
{name}`LiteralData.inserted`: INSERT only appends. Proof sketch: induction on the value
rows; each {name}`LiteralData.insertRow` keeps the old rows before the new one. -/
theorem LiteralData.mem_inserted {table : Table} {rows : List (List Value)} {row : Row}
    (member : row ∈ table.rows) : row ∈ (inserted table rows).rows := by
  induction rows generalizing table with
  | nil => exact member
  | cons values rest ih =>
    exact ih (by simp [insertRow, member])

/-- For every table and value rows, {name}`LiteralData.inserted` keeps the shape. Proof
sketch: induction on the value rows; each {name}`LiteralData.insertRow` keeps the shape. -/
theorem LiteralData.inserted_shape (table : Table) (rows : List (List Value)) :
    (inserted table rows).shape = table.shape := by
  induction rows generalizing table with
  | nil => rfl
  | cons values rest ih => exact (ih _).trans rfl

/-- For every valid table and value rows, assume each row has one value per column and
{name}`LiteralData.storedForm` for each column/value pair, and every rowid of the
inserted table is bounded. Then {name}`LiteralData.inserted` is valid. Proof sketch:
induction on the rows; each new row has a rowid that is a rowid of the final table, so
it is bounded, and {name}`Table.Valid.insertRow` adds it. -/
theorem Table.Valid.inserted {table : Table} {rows : List (List Value)} (valid : table.Valid)
    (each : ∀ values ∈ rows, values.length = table.shape.columns.length ∧
      (table.shape.columns.zip values).all (fun (column, value) => LiteralData.storedForm column.affinity value) = true)
    (bounded : (LiteralData.inserted table rows).rows.all (fun row => LiteralData.boundedInteger row.rowid) = true) :
    (LiteralData.inserted table rows).Valid := by
  induction rows generalizing table with
  | nil => exact valid
  | cons values rest ih =>
    obtain ⟨width, stored⟩ := each values (by simp)
    have newMember : ({ rowid := LiteralData.nextRowid table.rows, values } : Row) ∈
        (LiteralData.inserted table (values :: rest)).rows :=
      LiteralData.mem_inserted (rows := rest) (table := LiteralData.insertRow table values) (by simp [LiteralData.insertRow])
    have newBounded := List.all_eq_true.mp bounded _ newMember
    have validRow : validRowid (LiteralData.nextRowid table.rows) := by
      simpa [LiteralData.boundedInteger, validRowid] using newBounded
    exact ih (valid.insertRow validRow width (Row.Stored.of_storedForm stored))
      (fun values member => each values (List.mem_cons_of_mem _ member)) bounded

/-- For every profile, catalog, database, write position, result table, keys and
statement position: assume {name}`Conforms`, a table at the write position with the
result's shape, and a valid result. Then the database of {name}`checkedWrite` conforms:
it stores the result, or keeps the input database on a constraint failure. Proof
sketch: the success branch is {name}`Conforms.replaceRows`; the failure branch keeps the
database. -/
theorem checkedWrite_conforms {old result : Table} (conforms : Conforms profile catalog database)
    (present : database at_ = some old) (shape : result.shape = old.shape) (valid : result.Valid)
    (keys : List (List Nat)) (position : Nat) :
    Conforms profile catalog (checkedWrite database at_ keys result position).database := by
  unfold checkedWrite
  split
  · exact conforms.replaceRows present shape valid
  · exact conforms

/-- For every profile, catalog and database, and every INSERT that
{name}`statementReady` admits: if the database {name}`Conforms` to the catalog, so does
the database of its step, at every statement position. Proof sketch: without a table the
step fails and keeps the database; otherwise {name}`LiteralData.insertReady` gives the
premises of {name}`Table.Valid.inserted`, and {name}`checkedWrite_conforms` applies. -/
theorem literalStep_insert_conforms (conforms : Conforms profile catalog database)
    (ready : statementReady (.insert at_ rows keys returning) database = true) (position : Nat) :
    Conforms profile catalog (literalStep (.insert at_ rows keys returning) database position).database := by
  cases present : database at_ with
  | none => simp only [literalStep, present]; exact conforms
  | some table =>
    simp only [literalStep, present]
    simp only [statementReady, present, Option.all_some, LiteralData.insertReady, Bool.and_eq_true] at ready
    obtain ⟨⟨_, each⟩, bounded⟩ := ready
    have valid := (conforms.2 at_).2 table present
    refine checkedWrite_conforms conforms present (LiteralData.inserted_shape table rows) (valid.inserted ?_ bounded) _ _
    intro values member
    have check := List.all_eq_true.mp each values member
    simp only [Bool.and_eq_true, beq_iff_eq] at check
    exact ⟨check.1, check.2⟩

/-- For every profile, catalog and database, and every UPDATE: if the database
{name}`Conforms` to the catalog, so does the database of its step, at every statement
position. No admission premise is needed: {name}`Table.Valid.updated` holds for every
valid table. -/
theorem literalStep_update_conforms (conforms : Conforms profile catalog database)
    (position : Nat) :
    Conforms profile catalog (literalStep (.update at_ assignments filter keys returning) database position).database := by
  cases present : database at_ with
  | none => simp only [literalStep, present]; exact conforms
  | some table =>
    simp only [literalStep, present]
    exact checkedWrite_conforms conforms present (result := LiteralData.updated table assignments filter) rfl
      (((conforms.2 at_).2 table present).updated assignments filter) _ _

end Belay.Sqlite
