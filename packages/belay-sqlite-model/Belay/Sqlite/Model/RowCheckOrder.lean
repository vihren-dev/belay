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

/-- How a column gets its value: from the write, or generated {lit}`VIRTUAL` or {lit}`STORED`. -/
inductive ColumnKind where
  /-- A column that is not generated. -/
  | ordinary
  /-- A generated {lit}`VIRTUAL` column. -/
  | virtual
  /-- A generated {lit}`STORED` column. -/
  | stored
  deriving Repr, DecidableEq

/-- The kind of the column: ordinary, {lit}`VIRTUAL` or {lit}`STORED`. -/
def CatalogColumn.kind (column : CatalogColumn) : ColumnKind :=
  match column.generated with
  | none => .ordinary
  | some generated => if generated.stored then .stored else .virtual

/-- Whether the table has a generated column. -/
def CatalogTable.hasGenerated (shape : CatalogTable) : Bool := shape.columns.any (·.generated.isSome)

/-- Whether the table has a CHECK constraint ({name}`CatalogTable.allChecks`). -/
def CatalogTable.hasChecks (shape : CatalogTable) : Bool := !shape.allChecks.isEmpty

namespace LiteralData

/-- The first column of a {lit}`STRICT` table, in column order, whose cell does not fit its type
({name}`StrictType.fits`), with the cell; none when every cell fits. -/
def strictColumn (shape : CatalogTable) (row : Row) : Option (Nat × Value) :=
  ((shape.columns.zip row.values).zipIdx.find? fun ((column, value), _) =>
    !column.strictType.all (·.fits value)).map fun ((_, value), position) => (position, value)

/-- The NOT NULL failure of each row, among the columns that pass {lit}`keep`: the first such NOT
NULL column that holds NULL, at its position in the table. -/
def nullFailuresWhere (keep : CatalogColumn → Bool) (table : Table) : List TableFailure :=
  table.rows.filterMap fun row => ((table.shape.columns.zip row.values).findIdx? fun (column, value) =>
    keep column && (column.notNull && value == .null)).map .notNull

/-- The {lit}`STRICT` failure of each row among the columns of the kind: the first such column
whose cell does not fit its type, at its position in the table, with the cell. -/
def strictFailuresOf (kind : ColumnKind) (table : Table) : List TableFailure :=
  table.rows.filterMap fun row => (((table.shape.columns.zip row.values).zipIdx.find? fun ((column, value), _) =>
    column.kind == kind && !column.strictType.all (·.fits value)).map fun ((_, value), position) => (position, value)).map
      fun (column, value) => .strictType column value

/-- The type failures that SQLite finds before NOT NULL: in a table with a generated column, those
of the ordinary columns, then those of the {lit}`VIRTUAL` columns; none in another table. -/
def earlyTypeFailures (table : Table) : List TableFailure :=
  if table.shape.hasGenerated then strictFailuresOf .ordinary table ++ strictFailuresOf .virtual table else []

/-- The type failures of SQLite's late type check: in a table with a generated column, those of the
{lit}`STORED` columns; in another table, those of every column, which are all ordinary. -/
def lateTypeFailures (table : Table) : List TableFailure :=
  if table.shape.hasGenerated then strictFailuresOf .stored table
  else strictFailuresOf .ordinary table ++ strictFailuresOf .virtual table ++ strictFailuresOf .stored table

/-- The NOT NULL failures: those of the ordinary columns, then those of the generated columns. -/
def notNullFailures (table : Table) : List TableFailure :=
  nullFailuresWhere (·.kind == .ordinary) table ++ nullFailuresWhere (!·.kind == .ordinary) table

/-- The NOT NULL failure of each row over every column ({name}`nullColumn`). -/
def allNullFailures (table : Table) : List TableFailure :=
  table.rows.filterMap fun row => (nullColumn table.shape.columns row.values).map .notNull

/-- The {lit}`STRICT` failure of each row over every column ({name}`strictColumn`). -/
def allStrictFailures (table : Table) : List TableFailure :=
  table.rows.filterMap fun row => (strictColumn table.shape row).map fun (column, value) => .strictType column value

/-- For all predicates {lit}`keep` and {lit}`test` over a list: no element passes {lit}`keep` and
{lit}`test`, and no element fails {lit}`keep` and passes {lit}`test`, exactly when no element
passes {lit}`test`. Proof sketch: by cases on {lit}`keep` of each element. -/
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

/-- For every function {lit}`kindOf` to {name}`ColumnKind` and predicate {lit}`test` over a
list: for each of the three kinds, {lit}`find?` finds no element of the kind that passes
{lit}`test`, exactly when it finds no element that passes {lit}`test`. Proof sketch: by cases on
the kind of each element. -/
theorem find?_kinds_eq_none_iff {α : Type} (list : List α) (kindOf : α → ColumnKind) (test : α → Bool) :
    (list.find? (fun x => kindOf x == .ordinary && test x) = none ∧
      list.find? (fun x => kindOf x == .virtual && test x) = none ∧
      list.find? (fun x => kindOf x == .stored && test x) = none) ↔ list.find? test = none := by
  simp only [List.find?_eq_none]
  constructor
  · rintro ⟨ordinary, virtual, stored⟩ x member
    cases found : kindOf x
    · simpa [found] using ordinary x member
    · simpa [found] using virtual x member
    · simpa [found] using stored x member
  · intro none
    exact ⟨fun x member => by simp [none x member], fun x member => by simp [none x member],
      fun x member => by simp [none x member]⟩

/-- For every table: {name}`notNullFailures` is empty exactly when {name}`allNullFailures` is
empty. Proof sketch: for each row, the ordinary and the generated columns cover each column
({name}`findIdx?_split_eq_none_iff`). -/
theorem notNullFailures_eq_nil_iff (table : Table) : notNullFailures table = [] ↔ allNullFailures table = [] := by
  simp only [notNullFailures, allNullFailures, nullFailuresWhere, List.append_eq_nil_iff, List.filterMap_eq_nil_iff,
    Option.map_eq_none_iff, ← forall_and]
  refine forall_congr' fun row => imp_congr_right fun _ => ?_
  simpa [nullColumn] using findIdx?_split_eq_none_iff (table.shape.columns.zip row.values)
    (fun pair => pair.1.kind == .ordinary) (fun pair => pair.1.notNull && pair.2 == .null)

/-- For every table: {name}`earlyTypeFailures` and {name}`lateTypeFailures` are both empty exactly
when {name}`allStrictFailures` is empty. Proof sketch: with or without a generated column, the two
lists hold the failures of the three kinds of columns, which cover each column
({name}`find?_kinds_eq_none_iff`). -/
theorem typeFailures_eq_nil_iff (table : Table) :
    (earlyTypeFailures table = [] ∧ lateTypeFailures table = []) ↔ allStrictFailures table = [] := by
  have kinds : (strictFailuresOf .ordinary table = [] ∧ strictFailuresOf .virtual table = [] ∧
      strictFailuresOf .stored table = []) ↔ allStrictFailures table = [] := by
    simp only [strictFailuresOf, allStrictFailures, List.filterMap_eq_nil_iff, Option.map_eq_none_iff, ← forall_and]
    refine forall_congr' fun row => imp_congr_right fun _ => ?_
    simpa [strictColumn] using find?_kinds_eq_none_iff ((table.shape.columns.zip row.values).zipIdx)
      (fun entry => entry.1.1.kind) (fun entry => !entry.1.1.strictType.all (·.fits entry.1.2))
  rw [← kinds]
  unfold earlyTypeFailures lateTypeFailures
  split <;> simp only [List.append_eq_nil_iff, true_and, and_left_comm, and_comm]

end LiteralData
end Belay.Sqlite.Model
