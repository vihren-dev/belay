import Belay.Sqlite.Model.LiteralPreservationLaws

set_option doc.verso true

/-! The checks that decide the facts of an admitted database (ADR 0022, D1). Each check
computes; a lemma states that it gives {lean}`true` exactly when its fact holds, and a
{lit}`Decidable` instance decides the fact with it, so {lit}`decide +kernel` proves a fact, or
its negation, for a concrete database. -/

namespace Belay.Sqlite.Model

/-- For every table at a position of a database, the position is below the catalog's length:
{name}`Database.table` gives no table past the end. Proof sketch: a table comes from a catalog
entry at the position, and a successful list lookup gives the bound. -/
theorem Database.table_lt {database : Database} {position : Nat} {table : Table}
    (present : database.table position = some table) : position < database.catalog.length := by
  unfold Database.table Catalog.tableAt at present
  cases found : database.catalog[position]? with
  | none => simp [found] at present
  | some _ => exact (List.getElem?_eq_some_iff.mp found).1

/-- Check a property at every table of a database: for each catalog position, the check of the
table there, and {lean}`true` at a position without a table. -/
def Database.everyTable (check : Nat → Table → Bool) (database : Database) : Bool :=
  (List.range database.catalog.length).all fun position => (database.table position).all (check position)

/-- For every check and property that agree at each position and table, and every database,
{name}`Database.everyTable` of the check is {lean}`true` exactly when the database satisfies
{name}`Database.EveryTable` of the property. Proof sketch: every table is at a position below
the catalog's length ({name}`Database.table_lt`). -/
theorem Database.everyTable_iff {check : Nat → Table → Bool} {property : Nat → Table → Prop}
    (agree : ∀ position table, check position table = true ↔ property position table) (database : Database) :
    database.everyTable check = true ↔ database.EveryTable property := by
  simp only [Database.everyTable, List.all_eq_true, List.mem_range]
  constructor
  · intro all position table present
    have checked := all position (Database.table_lt present)
    rw [present] at checked
    exact (agree position table).mp (by simpa using checked)
  · intro every position _
    cases present : database.table position with
    | none => rfl
    | some table => simpa using (agree position table).mpr (every position table present)

/-- Decide {name}`Database.EveryTable` with {name}`Database.everyTable` of the given check. -/
def Database.decideEveryTable {property : Nat → Table → Prop} (check : Nat → Table → Bool)
    (agree : ∀ position table, check position table = true ↔ property position table) (database : Database) :
    Decidable (database.EveryTable property) :=
  decidable_of_iff _ (Database.everyTable_iff agree database)

/-- Check {name}`Table.RowidsInRange`: each rowid satisfies {name}`LiteralData.boundedInteger`. -/
def Table.rowidsInRange (table : Table) : Bool := table.rows.all (LiteralData.boundedInteger ·.rowid)

/-- Check {name}`Table.RowsWide`: each row has as many cells as the table has columns. -/
def Table.rowsWide (table : Table) : Bool := table.rows.all (·.values.length == table.shape.columns.length)

/-- Check {name}`Table.RowsStored`: each row satisfies {name}`Row.Stored`, decided by
{name}`Row.decidableStored`. -/
def Table.rowsStored (table : Table) : Bool := table.rows.all fun row => decide (row.Stored table.shape.columns)

/-- Check {name}`Table.RowsAliased`: with a rowid alias, each row's cell there is its rowid. -/
def Table.rowsAliased (table : Table) : Bool :=
  table.rows.all fun row => table.shape.rowidAlias.all fun position => row.values[position]? == some (.integer row.rowid)

/-- For every table, {name}`LiteralData.rowidsDistinct` is {lean}`true` exactly when the table
satisfies {name}`Table.RowidsDistinct`. -/
theorem Table.rowidsDistinct_iff (table : Table) : LiteralData.rowidsDistinct table = true ↔ table.RowidsDistinct := by
  simp [LiteralData.rowidsDistinct, Table.RowidsDistinct]

/-- For every table, {name}`Table.rowidsInRange` is {lean}`true` exactly when the table
satisfies {name}`Table.RowidsInRange`. -/
theorem Table.rowidsInRange_iff (table : Table) : table.rowidsInRange = true ↔ table.RowidsInRange := by
  simp [Table.rowidsInRange, Table.RowidsInRange, LiteralData.boundedInteger, validRowid]

/-- For every table, {name}`Table.rowsWide` is {lean}`true` exactly when the table satisfies
{name}`Table.RowsWide`. -/
theorem Table.rowsWide_iff (table : Table) : table.rowsWide = true ↔ table.RowsWide := by
  simp [Table.rowsWide, Table.RowsWide]

/-- For every table, {name}`Table.rowsStored` is {lean}`true` exactly when the table satisfies
{name}`Table.RowsStored`. -/
theorem Table.rowsStored_iff (table : Table) : table.rowsStored = true ↔ table.RowsStored := by
  simp [Table.rowsStored, Table.RowsStored]

/-- For every table, {name}`Table.rowsAliased` is {lean}`true` exactly when the table satisfies
{name}`Table.RowsAliased`. -/
theorem Table.rowsAliased_iff (table : Table) : table.rowsAliased = true ↔ table.RowsAliased := by
  simp only [Table.rowsAliased, Table.RowsAliased, Row.Aliased, List.all_eq_true]
  refine forall_congr' fun row => imp_congr_right fun _ => ?_
  cases table.shape.rowidAlias <;> simp

/-- Decide {name}`Database.RowidsDistinct` with {name}`LiteralData.rowidsDistinct`. -/
instance Database.decidableRowidsDistinct (database : Database) : Decidable database.RowidsDistinct :=
  database.decideEveryTable (fun _ table => LiteralData.rowidsDistinct table) fun _ => Table.rowidsDistinct_iff
/-- Decide {name}`Database.RowidsInRange` with {name}`Table.rowidsInRange`. -/
instance Database.decidableRowidsInRange (database : Database) : Decidable database.RowidsInRange :=
  database.decideEveryTable (fun _ table => table.rowidsInRange) fun _ => Table.rowidsInRange_iff
/-- Decide {name}`Database.RowsWide` with {name}`Table.rowsWide`. -/
instance Database.decidableRowsWide (database : Database) : Decidable database.RowsWide :=
  database.decideEveryTable (fun _ table => table.rowsWide) fun _ => Table.rowsWide_iff
/-- Decide {name}`Database.RowsStored` with {name}`Table.rowsStored`. -/
instance Database.decidableRowsStored (database : Database) : Decidable database.RowsStored :=
  database.decideEveryTable (fun _ table => table.rowsStored) fun _ => Table.rowsStored_iff
/-- Decide {name}`Database.RowsAliased` with {name}`Table.rowsAliased`. -/
instance Database.decidableRowsAliased (database : Database) : Decidable database.RowsAliased :=
  database.decideEveryTable (fun _ table => table.rowsAliased) fun _ => Table.rowsAliased_iff

/-- Check {name}`Database.RowsShaped`: one row list for each catalog object, and an empty list
at each position below the end that holds no table. -/
def Database.rowsShaped (database : Database) : Bool :=
  database.rows.length == database.catalog.length &&
    (List.range database.rows.length).all fun position =>
      (database.catalog.tableAt position).isSome || (database.rows.getD position []).isEmpty

/-- For every database, {name}`Database.rowsShaped` is {lean}`true` exactly when the database
satisfies {name}`Database.RowsShaped`. Proof sketch: past the end of {lit}`rows`,
{lit}`List.getD` gives the empty list. -/
theorem Database.rowsShaped_iff (database : Database) : database.rowsShaped = true ↔ database.RowsShaped := by
  simp only [Database.rowsShaped, Database.RowsShaped, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Option.isSome_iff_ne_none, List.isEmpty_iff]
  refine and_congr_right fun _ => ⟨fun all position absent => ?_, fun every position _ => ?_⟩
  · by_cases below : position < database.rows.length
    · exact (all position below).resolve_left (by simpa using absent)
    · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : database.rows.length ≤ position)]
  · by_cases absent : database.catalog.tableAt position = none
    · exact Or.inr (every position absent)
    · exact Or.inl absent

/-- Decide {name}`Database.RowsShaped` with {name}`Database.rowsShaped`. -/
instance Database.decidableRowsShaped (database : Database) : Decidable database.RowsShaped :=
  decidable_of_iff _ database.rowsShaped_iff

/-- Decide {name}`Database.Admitted` through the decisions of its fields. -/
instance Database.decidableAdmitted (profile : Profile) (database : Database) : Decidable (database.Admitted profile) :=
  decidable_of_iff (database.catalog.Valid profile.limits ∧ database.RowsShaped ∧ database.RowidsDistinct ∧
      database.RowidsInRange ∧ database.RowsWide ∧ database.RowsStored ∧ database.RowsAliased)
    ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩, fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩⟩

end Belay.Sqlite.Model
