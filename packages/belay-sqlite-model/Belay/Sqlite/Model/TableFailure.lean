import Belay.Sqlite.Model.RowCheckOrder

set_option doc.verso true

/-! What fails in a table that a write checks, read off the checks of
{name}`Belay.Sqlite.Model.LiteralData.constraints` and
{name}`Belay.Sqlite.Model.LiteralData.rowidsDistinct`, so that a message can name the
constraint. The failures are in SQLite's order of checks for one row (SQLite 3.51, measured with
the {lit}`sqlite3` shell): the early types and NOT NULL ({lit}`RowCheckOrder.lean`), the late
types when the write runs a CHECK constraint, CHECK, the rowid, the late types when the write runs
no CHECK constraint, and the unique keys. -/

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

/-- The failures that SQLite finds before the rowid check, in its order: the early types
({name}`earlyTypeFailures`), NOT NULL ({name}`notNullFailures`), the late types
({name}`lateTypeFailures`) when {lit}`lateFirst` is {lean}`true`, and the CHECK constraint of each
row ({name}`failingCheck`). {lit}`lateFirst` says whether the write runs a CHECK constraint
({name}`CatalogTable.hasChecks` for an INSERT, {name}`CatalogTable.updateRunsChecks` for an
UPDATE). -/
def beforeRowidFailures (lateFirst : Bool) (table : Table) : List TableFailure :=
  earlyTypeFailures table ++ notNullFailures table ++ (if lateFirst then lateTypeFailures table else []) ++
  table.rows.filterMap (fun row => (failingCheck table.shape row).map (.check ·.label))

/-- The failures that SQLite finds after the rowid check and before the keys: the late types
({name}`lateTypeFailures`) when {lit}`lateFirst` is {lean}`false`. -/
def afterRowidFailures (lateFirst : Bool) (table : Table) : List TableFailure :=
  if lateFirst then [] else lateTypeFailures table

/-- Every failure of the table, in SQLite's order: {name}`beforeRowidFailures`, a repeated rowid
({name}`rowidsDistinct`), {name}`afterRowidFailures`, and the keys that fail
({name}`failingKeys`), if any. -/
def tableFailuresWith (lateFirst : Bool) (keys : List UniqueKey) (table : Table) : List TableFailure :=
  beforeRowidFailures lateFirst table ++ (if rowidsDistinct table then [] else [.rowid]) ++
  afterRowidFailures lateFirst table ++ (match failingKeys keys table with | [] => [] | failing@(_ :: _) => [.keys failing])

/-- Every failure of the table for a write that runs each CHECK constraint, as an INSERT does
({name}`tableFailuresWith` of {name}`CatalogTable.hasChecks`). -/
def tableFailures (keys : List UniqueKey) (table : Table) : List TableFailure :=
  tableFailuresWith table.shape.hasChecks keys table

/-- The first failure of the table ({name}`tableFailuresWith`), none when the table has none. -/
def firstFailureWith (lateFirst : Bool) (keys : List UniqueKey) (table : Table) : Option TableFailure :=
  (tableFailuresWith lateFirst keys table).head?

/-- The first failure of the table ({name}`tableFailures`), none when the table has none. -/
def firstFailure (keys : List UniqueKey) (table : Table) : Option TableFailure :=
  firstFailureWith table.shape.hasChecks keys table

/-- The failure of one row by itself: the first NOT NULL, {lit}`STRICT` or CHECK failure, in
SQLite's order ({name}`firstFailure` of a table of the row alone, with no key). SQLite checks
these before the keys of the row. -/
def rowFailure (shape : CatalogTable) (row : Row) : Option TableFailure :=
  firstFailure [] { shape, rows := [row] }

/-- For every flag, list of keys and table: {name}`tableFailuresWith` is empty exactly when the
list of the same failures in the order NOT NULL, types, CHECK, rowid, keys is empty. Proof sketch:
emptiness of a concatenation does not depend on the order of its parts;
{name}`notNullFailures_eq_nil_iff` and {name}`typeFailures_eq_nil_iff` replace the groups by the
checks over every column. -/
theorem tableFailuresWith_eq_nil_iff_ordered (lateFirst : Bool) (keys : List UniqueKey) (table : Table) :
    tableFailuresWith lateFirst keys table = [] ↔ (allNullFailures table ++ allStrictFailures table ++
      table.rows.filterMap (fun row => (failingCheck table.shape row).map (.check ·.label)) ++
      (if rowidsDistinct table then [] else [.rowid]) ++
      (match failingKeys keys table with | [] => [] | failing@(_ :: _) => [.keys failing])) = [] := by
  have types := typeFailures_eq_nil_iff table
  simp only [List.append_eq_nil_iff, ← notNullFailures_eq_nil_iff, ← types, tableFailuresWith, beforeRowidFailures,
    afterRowidFailures]
  cases lateFirst <;> simp only [Bool.false_eq_true, ↓reduceIte, and_assoc, and_left_comm, and_comm, true_and]

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

/-- For every flag, list of keys and table: {name}`tableFailuresWith` is empty exactly when the
table passes {name}`constraints` of the keys and {name}`rowidsDistinct`, the checks with which a
write fails. So the failures are those of the write's own checks, not of a second definition.
Proof sketch: the order of the failures does not matter
({name}`tableFailuresWith_eq_nil_iff_ordered`); each
part of the list is empty exactly when its check passes; NOT NULL and CHECK compare
by the first failing element, and the keys by {name}`failingKeys_eq_nil_iff`. -/
theorem tableFailuresWith_eq_nil_iff (lateFirst : Bool) (keys : List UniqueKey) (table : Table) :
    tableFailuresWith lateFirst keys table = [] ↔ (constraints keys table && rowidsDistinct table) = true := by
  have keysNil := failingKeys_eq_nil_iff keys table
  rw [tableFailuresWith_eq_nil_iff_ordered]
  simp only [allNullFailures, allStrictFailures, List.append_eq_nil_iff, List.filterMap_eq_nil_iff, Option.map_eq_none_iff,
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

/-- For every list of keys and table: {name}`tableFailures` is empty exactly when the table passes
{name}`constraints` of the keys and {name}`rowidsDistinct`. Proof sketch: it is
{name}`tableFailuresWith_eq_nil_iff` for one flag. -/
theorem tableFailures_eq_nil_iff (keys : List UniqueKey) (table : Table) :
    tableFailures keys table = [] ↔ (constraints keys table && rowidsDistinct table) = true :=
  tableFailuresWith_eq_nil_iff _ keys table

/-- For every flag, list of keys and table that fails {name}`constraints` of the keys or
{name}`rowidsDistinct`: {name}`firstFailureWith` gives some failure. Proof sketch: the head of a
list is none only when the list is empty, which {name}`tableFailuresWith_eq_nil_iff` excludes. -/
theorem firstFailureWith_isSome {lateFirst : Bool} {keys : List UniqueKey} {table : Table}
    (fails : ¬(constraints keys table && rowidsDistinct table) = true) :
    (firstFailureWith lateFirst keys table).isSome := by
  cases found : firstFailureWith lateFirst keys table with
  | some _ => rfl
  | none =>
    rw [firstFailureWith, List.head?_eq_none_iff, tableFailuresWith_eq_nil_iff] at found
    exact absurd found fails

/-- For every list of keys and table: {name}`firstFailure` is none exactly when the table passes
{name}`constraints` of the keys and {name}`rowidsDistinct`. Proof sketch: the head of a list is
none exactly when the list is empty ({name}`tableFailuresWith_eq_nil_iff`). -/
theorem firstFailure_eq_none_iff (keys : List UniqueKey) (table : Table) :
    firstFailure keys table = none ↔ (constraints keys table && rowidsDistinct table) = true := by
  rw [firstFailure, firstFailureWith, List.head?_eq_none_iff, tableFailuresWith_eq_nil_iff]

/-- For every list of keys and table that fails {name}`constraints` of the keys or
{name}`rowidsDistinct`: {name}`firstFailure` gives some failure. Proof sketch: it is
{name}`firstFailureWith_isSome` for one flag. -/
theorem firstFailure_isSome {keys : List UniqueKey} {table : Table}
    (fails : ¬(constraints keys table && rowidsDistinct table) = true) : (firstFailure keys table).isSome :=
  firstFailureWith_isSome fails

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
