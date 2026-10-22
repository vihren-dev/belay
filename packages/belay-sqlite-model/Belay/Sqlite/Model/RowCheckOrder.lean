import Belay.Sqlite.Model.UpsertRun

set_option doc.verso true

/-! The order in which SQLite checks the NOT NULL columns and the {lit}`STRICT` types of a row
(SQLite 3.51, measured with the {lit}`sqlite3` shell). In a table without a generated column,
SQLite checks NOT NULL, then the types. In a table with a generated column, it checks the types
of the columns that are not generated, then the types of the generated columns, then NOT NULL of
the columns that are not generated, then NOT NULL of the generated columns. In each group, the
order is the column order. {lit}`TableFailure.lean` puts the CHECK constraints, the rowid and
the keys after these failures. -/

namespace Belay.Sqlite.Model

/-- One failure of a table that a write checks. For example, a NULL in the second column, which
is NOT NULL, is {lean}`TableFailure.notNull 1`. -/
inductive TableFailure where
  /-- The NOT NULL column at the position holds NULL. -/
  | notNull (column : Nat)
  /-- The value does not fit the type of the {lit}`STRICT` column at the position. -/
  | strictType (column : Nat) (value : Value)
  /-- The CHECK constraint with the label is false for a row. -/
  | check (label : String)
  /-- Two rows have the same rowid. -/
  | rowid
  /-- Two rows conflict on each unique key at the positions (in the list of the keys). -/
  | keys (failing : List Nat)
  deriving Repr, DecidableEq

/-- Whether the column is generated, or, for {lean}`false`, not generated. -/
def CatalogColumn.isGeneratedAs (generated : Bool) (column : CatalogColumn) : Bool :=
  column.generated.isSome == generated

/-- For every column: it is not generated exactly when it is not generated as true. -/
theorem CatalogColumn.isGeneratedAs_false (column : CatalogColumn) :
    column.isGeneratedAs false = !column.isGeneratedAs true := by
  simp only [CatalogColumn.isGeneratedAs]; cases column.generated <;> rfl

namespace LiteralData

/-- The first column of a {lit}`STRICT` table, in column order, whose cell does not fit its type
({name}`StrictType.fits`), with the cell; none when every cell fits. -/
def strictColumn (shape : CatalogTable) (row : Row) : Option (Nat × Value) :=
  ((shape.columns.zip row.values).zipIdx.find? fun ((column, value), _) =>
    !column.strictType.all (·.fits value)).map fun ((_, value), position) => (position, value)

/-- {name}`nullColumn` among the columns that are generated, or not generated
({name}`CatalogColumn.isGeneratedAs`): the first such NOT NULL column that holds NULL, at its
position in the table. -/
def nullColumnAmong (generated : Bool) (columns : List CatalogColumn) (values : List Value) : Option Nat :=
  (columns.zip values).findIdx? fun (column, value) =>
    column.isGeneratedAs generated && (column.notNull && value == .null)

/-- {name}`strictColumn` among the columns that are generated, or not generated: the first such
column whose cell does not fit its type, at its position in the table, with the cell. -/
def strictColumnAmong (generated : Bool) (shape : CatalogTable) (row : Row) : Option (Nat × Value) :=
  ((shape.columns.zip row.values).zipIdx.find? fun ((column, value), _) =>
    column.isGeneratedAs generated && !column.strictType.all (·.fits value)).map
      fun ((_, value), position) => (position, value)

/-- The NOT NULL failures of each row among the columns that are generated, or not generated. -/
def nullFailures (generated : Bool) (table : Table) : List TableFailure :=
  table.rows.filterMap fun row => (nullColumnAmong generated table.shape.columns row.values).map .notNull

/-- The {lit}`STRICT` failures of each row among the columns that are generated, or not
generated. -/
def strictFailures (generated : Bool) (table : Table) : List TableFailure :=
  table.rows.filterMap fun row =>
    (strictColumnAmong generated table.shape row).map fun (column, value) => .strictType column value

/-- The NOT NULL and {lit}`STRICT` failures of the table, in SQLite's order of checks (see the
module docstring). -/
def columnFailures (table : Table) : List TableFailure :=
  if table.shape.columns.any (·.generated.isSome) then
    strictFailures false table ++ strictFailures true table ++ nullFailures false table ++ nullFailures true table
  else nullFailures false table ++ nullFailures true table ++ strictFailures false table ++ strictFailures true table

/-- For every predicate {lit}`keep` and {lit}`test` over a list: no element passes
{lit}`keep` and {lit}`test`, and no element fails {lit}`keep` and passes {lit}`test`, exactly when no
element passes {lit}`test`. -/
theorem findIdx?_split_eq_none_iff {α : Type} (list : List α) (keep test : α → Bool) :
    (list.findIdx? (fun x => keep x && test x) = none ∧ list.findIdx? (fun x => !keep x && test x) = none) ↔
      list.findIdx? test = none := by
  simp only [List.findIdx?_eq_none_iff]
  constructor
  · intro ⟨kept, other⟩ x member
    cases found : keep x
    · simpa [found] using other x member
    · simpa [found] using kept x member
  · intro none
    exact ⟨fun x member => by simp [none x member], fun x member => by simp [none x member]⟩

/-- For every predicate {lit}`keep` and {lit}`test` over a list: {lit}`find?` finds no element that
passes {lit}`keep` and {lit}`test`, and none that fails {lit}`keep` and passes {lit}`test`, exactly
when it finds no element that passes {lit}`test`. -/
theorem find?_split_eq_none_iff {α : Type} (list : List α) (keep test : α → Bool) :
    (list.find? (fun x => keep x && test x) = none ∧ list.find? (fun x => !keep x && test x) = none) ↔
      list.find? test = none := by
  simp only [List.find?_eq_none]
  constructor
  · intro ⟨kept, other⟩ x member
    cases found : keep x
    · simpa [found] using other x member
    · simpa [found] using kept x member
  · intro none
    exact ⟨fun x member => by simp [none x member], fun x member => by simp [none x member]⟩

/-- For every table: {name}`columnFailures` is empty exactly when no row has a NULL in a NOT NULL
column ({name}`nullColumn`) and no row has a cell that does not fit its {lit}`STRICT` type
({name}`strictColumn`), whatever the order of the checks. Proof sketch: the columns that are
generated and those that are not cover each column, so the two lists of a check are empty
exactly when the check over every column finds nothing ({name}`findIdx?_split_eq_none_iff`,
{name}`find?_split_eq_none_iff`). -/
theorem columnFailures_eq_nil_iff (table : Table) :
    columnFailures table = [] ↔
      (table.rows.filterMap (fun row => (nullColumn table.shape.columns row.values).map TableFailure.notNull) = [] ∧
        table.rows.filterMap (fun row => (strictColumn table.shape row).map fun (column, value) =>
          TableFailure.strictType column value) = []) := by
  have nulls : (nullFailures false table = [] ∧ nullFailures true table = []) ↔
      table.rows.filterMap (fun row => (nullColumn table.shape.columns row.values).map TableFailure.notNull) = [] := by
    simp only [nullFailures, List.filterMap_eq_nil_iff, Option.map_eq_none_iff, ← forall_and]
    refine forall_congr' fun row => imp_congr_right fun _ => ?_
    have split := findIdx?_split_eq_none_iff (table.shape.columns.zip row.values)
      (fun pair => pair.1.isGeneratedAs true) (fun pair => pair.1.notNull && pair.2 == .null)
    simp only [nullColumnAmong, nullColumn]
    simpa [CatalogColumn.isGeneratedAs_false, and_comm] using split
  have stricts : (strictFailures false table = [] ∧ strictFailures true table = []) ↔
      table.rows.filterMap (fun row => (strictColumn table.shape row).map fun (column, value) =>
        TableFailure.strictType column value) = [] := by
    simp only [strictFailures, List.filterMap_eq_nil_iff, Option.map_eq_none_iff, ← forall_and]
    refine forall_congr' fun row => imp_congr_right fun _ => ?_
    have split := find?_split_eq_none_iff ((table.shape.columns.zip row.values).zipIdx)
      (fun entry => entry.1.1.isGeneratedAs true) (fun entry => !entry.1.1.strictType.all (·.fits entry.1.2))
    simp only [strictColumnAmong, strictColumn]
    simpa [CatalogColumn.isGeneratedAs_false, and_comm] using split
  rw [← nulls, ← stricts]
  unfold columnFailures
  split <;> simp only [List.append_eq_nil_iff, and_assoc, and_left_comm, and_comm]

end LiteralData
end Belay.Sqlite.Model
