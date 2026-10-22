import Belay.Sqlite.Model.RowCheckOrder

set_option doc.verso true

/-! What fails in a table that a write checks, read off the checks of
{name}`Belay.Sqlite.Model.LiteralData.constraints` and
{name}`Belay.Sqlite.Model.LiteralData.rowidsDistinct`, so that a message can name the
constraint. The failures are in SQLite's order of checks for one row (SQLite 3.51, measured with
the {lit}`sqlite3` shell): NOT NULL and the types of a {lit}`STRICT` table in the order of
{lit}`RowCheckOrder.lean`, then CHECK, then the rowid, then the unique keys. -/

namespace Belay.Sqlite.Model

namespace LiteralData

/-- The first CHECK constraint of the table, in the order of {name}`CatalogTable.allChecks`, that
the row fails ({name}`checkHolds`); none when the row passes them all. -/
def failingCheck (shape : CatalogTable) (row : Row) : Option CheckConstraint :=
  shape.allChecks.find? fun check => !checkHolds row check

/-- The positions of the keys on which two rows of the table conflict ({name}`uniqueRows`), in
the order of the keys. -/
def failingKeys (keys : List UniqueKey) (table : Table) : List Nat :=
  (keys.zipIdx.filter fun (key, _) => !uniqueRows key table.rows).map (·.2)

/-- Every failure of the table, in this order: the NOT NULL and {lit}`STRICT` failures of each row
in SQLite's order ({name}`columnFailures`), the CHECK constraint of each row
({name}`failingCheck`), a repeated rowid ({name}`rowidsDistinct`), and the keys that fail
({name}`failingKeys`), if any. -/
def tableFailures (keys : List UniqueKey) (table : Table) : List TableFailure :=
  columnFailures table ++
  table.rows.filterMap (fun row => (failingCheck table.shape row).map (.check ·.label)) ++
  (if rowidsDistinct table then [] else [.rowid]) ++
  (match failingKeys keys table with | [] => [] | failing@(_ :: _) => [.keys failing])

/-- The first failure of the table ({name}`tableFailures`), none when the table has none. -/
def firstFailure (keys : List UniqueKey) (table : Table) : Option TableFailure :=
  (tableFailures keys table).head?

/-- The failure of one row by itself: the first NOT NULL, {lit}`STRICT` or CHECK failure, in
SQLite's order
({name}`firstFailure` of a table of the row alone, with no key). SQLite checks these before the
keys of the row. -/
def rowFailure (shape : CatalogTable) (row : Row) : Option TableFailure :=
  firstFailure [] { shape, rows := [row] }

/-- For every list of keys and table: {name}`failingKeys` is empty exactly when
{name}`keysUnique` is {lean}`true`. Proof sketch: both say that each key passes
{name}`uniqueRows`; a key and its position in {lit}`zipIdx` give one another. -/
theorem failingKeys_eq_nil_iff (keys : List UniqueKey) (table : Table) :
    failingKeys keys table = [] ↔ keysUnique keys table = true := by
  simp only [failingKeys, keysUnique, List.map_eq_nil_iff, List.filter_eq_nil_iff, List.all_eq_true,
    Bool.not_eq_true', Bool.not_eq_false]
  constructor
  · intro all key member
    obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp member
    have : (key, index) ∈ keys.zipIdx := by simp [List.mem_zipIdx_iff_getElem?, found]
    simpa using all _ this
  · intro all pair member
    exact all _ (List.fst_mem_of_mem_zipIdx member)

/-- For every list of keys and table: {name}`tableFailures` is empty exactly when the table
passes {name}`constraints` of the keys and {name}`rowidsDistinct`, the checks with which a write
fails. So the failures are those of the write's own checks, not of a second definition. Proof
sketch: each part of the list is empty exactly when its check passes ({name}`columnFailures_eq_nil_iff`
for NOT NULL and the types, whatever their order); NOT NULL and CHECK compare
by the first failing element, and the keys by {name}`failingKeys_eq_nil_iff`. -/
theorem tableFailures_eq_nil_iff (keys : List UniqueKey) (table : Table) :
    tableFailures keys table = [] ↔ (constraints keys table && rowidsDistinct table) = true := by
  have keysNil := failingKeys_eq_nil_iff keys table
  simp only [tableFailures, List.append_eq_nil_iff, columnFailures_eq_nil_iff, List.filterMap_eq_nil_iff, Option.map_eq_none_iff,
    constraints, notNullRows, typedRows, checkedRows, checksHold, typesFit, Bool.and_eq_true,
    List.all_eq_true, nullColumn, List.findIdx?_eq_none_iff, failingCheck, List.find?_eq_none,
    strictColumn, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨⟨⟨nulls, types⟩, checks⟩, rowids⟩, keyFails⟩
    refine ⟨⟨⟨⟨fun row hrow pair hpair => ?_, fun row hrow pair hpair => ?_⟩, fun row hrow check hcheck => ?_⟩,
      keysNil.mp ?_⟩, ?_⟩
    · have := nulls row hrow pair hpair; revert this; cases pair.1.notNull <;> simp
    · obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp hpair
      have := types row hrow (pair, index) (by simp [List.mem_zipIdx_iff_getElem?, found]); simpa using this
    · have := checks row hrow check hcheck; simpa using this
    · split at keyFails <;> simp_all
    · revert rowids; split <;> simp_all
  · rintro ⟨⟨⟨⟨nulls, types⟩, checks⟩, keysOk⟩, rowids⟩
    refine ⟨⟨⟨⟨fun row hrow pair hpair => ?_, fun row hrow pair hpair => ?_⟩, fun row hrow check hcheck => ?_⟩,
      by simp [rowids]⟩, ?_⟩
    · have := nulls row hrow pair hpair; revert this; cases pair.1.notNull <;> simp
    · have := types row hrow pair.1 (List.fst_mem_of_mem_zipIdx hpair); simpa using this
    · have := checks row hrow check hcheck; simpa using this
    · rw [keysNil.mpr keysOk]

/-- For every list of keys and table: {name}`firstFailure` is none exactly when the table passes
{name}`constraints` of the keys and {name}`rowidsDistinct`. Proof sketch: the head of a list is
none exactly when the list is empty ({name}`tableFailures_eq_nil_iff`). -/
theorem firstFailure_eq_none_iff (keys : List UniqueKey) (table : Table) :
    firstFailure keys table = none ↔ (constraints keys table && rowidsDistinct table) = true := by
  rw [firstFailure, List.head?_eq_none_iff, tableFailures_eq_nil_iff]

/-- For every list of keys and table that fails {name}`constraints` of the keys or
{name}`rowidsDistinct`: {name}`firstFailure` gives some failure. Proof sketch: if it gave none,
{name}`firstFailure_eq_none_iff` would give the checks that the table fails. -/
theorem firstFailure_isSome {keys : List UniqueKey} {table : Table}
    (fails : ¬(constraints keys table && rowidsDistinct table) = true) : (firstFailure keys table).isSome := by
  cases found : firstFailure keys table with
  | some _ => rfl
  | none => exact absurd ((firstFailure_eq_none_iff _ _).mp found) fails

/-- For every table shape and row: if {name}`rowFailure` gives none, then the row has no NULL in
a NOT NULL column ({name}`nullColumn` is none), and it passes {name}`typesFit` and
{name}`checksHold`. Proof sketch: a table of the row alone passes {name}`constraints`
({name}`firstFailure_eq_none_iff`), whose checks of the one row are these three. -/
theorem rowFailure_eq_none {shape : CatalogTable} {row : Row} (passes : rowFailure shape row = none) :
    nullColumn shape.columns row.values = none ∧ typesFit shape row = true ∧ checksHold shape row = true := by
  have holds := (firstFailure_eq_none_iff _ _).mp passes
  simp only [constraints, notNullRows, typedRows, checkedRows, Bool.and_eq_true, List.all_cons, List.all_nil,
    Bool.and_true] at holds
  obtain ⟨⟨⟨⟨nulls, types⟩, checks⟩, _⟩, _⟩ := holds
  refine ⟨?_, types, checks⟩
  simp only [nullColumn, List.findIdx?_eq_none_iff]
  intro pair member
  have := (List.all_eq_true.mp nulls) pair member
  revert this; cases pair.1.notNull <;> simp

end LiteralData
end Belay.Sqlite.Model
