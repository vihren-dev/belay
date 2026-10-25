import Belay

/-! Installed consumers of the normalized-field row and query laws, including
arbitrary values and a nonempty table. -/

set_option doc.verso true

namespace NormalizedFieldFixture
open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved Belay.Sqlite.Model.NormalizedField

/-- A nonempty table whose email cell can have any storage class. The declared
BLOB affinity retains that supplied value, and the first column aliases rowid. -/
def input (value : Value) : Table :=
  { shape := {
      columns := [{ name := name! "id", declaredType := some "INTEGER" },
        { name := name! "email", declaredType := none }]
      primaryKey := [0]
      rowidAlias := some 0 }
    rows := [{ rowid := 1, values := [.integer 1, value] }] }

/-- The plain TEXT field used by the actual appended-cell UPDATE. -/
def lowered : CatalogColumn := { name := name! "email_lower", declaredType := some "TEXT" }

/-- The real assignment evaluator appends the correct lowercase value for every
input Value on this nonempty table. Proof sketch: discharge the structural
premises of the universal row-map theorem from the concrete two-column schema. -/
theorem backfill_for_every_value (value : Value) :
    (LiteralData.updated (EvalContext.plain 0) ((input value).appendColumns [(lowered, .null)])
      [(2, .scalar .lower (.cons (.column 1) .nil))] none).rows =
      [{ rowid := 1, values := [.integer 1, value, mapText lowerByte value] }] := by
  have rows := updated_lower_append (EvalContext.plain 0) (input value) lowered 1
    (by simp [Table.RowsWide, input])
    (by simp [Table.RowsAliased, Row.Aliased, input])
    (by simp [input]) (by simp [input]) rfl rfl
  simpa [input, Row.appendValues] using rows

/-- Every parameter Value, including NULL and nontext values, has the same lookup
result after the corresponding lowercase cell is appended. Proof sketch: apply
the generic result theorem with the two-cell row and its existing ID position. -/
theorem lookup_for_every_parameter (value parameter : Value) :
    (Query.simple [] (some (storedFilter 2 1)) [.scalar (.column 0)] ["id"]).results
        { EvalContext.plain 0 with parameters := [parameter] }
        [[.integer 1, value, mapText lowerByte value]] =
      (Query.simple [] (some (originalFilter 1 1)) [.scalar (.column 0)] ["id"]).results
        { EvalContext.plain 0 with parameters := [parameter] } [[.integer 1, value]] := by
  simpa using results_translate
    { EvalContext.plain 0 with parameters := [parameter] }
    [[.integer 1, value]] [] [] 2 1 0 1 (by simp) (by decide)

/-- Concrete lookups include all five Value constructors: NULL matches nothing,
and integer, REAL, TEXT and BLOB inputs match their own lowercase lookup. Proof
sketch: kernel evaluation of the existing simple-query result function. -/
theorem five_value_kinds :
    ([Value.null, .integer 42, .real 4607182418800017408,
      .text (bytes! "ALPHA"), .blob (bytes! "BETA")].map fun value =>
        (Query.simple [] (some (storedFilter 2 1)) [.scalar (.column 0)] ["id"]).results
          { EvalContext.plain 0 with parameters := [value] }
          [[.integer 1, value, mapText lowerByte value]]) =
      [[], [[.integer 1]], [[.integer 1]], [[.integer 1]], [[.integer 1]]] := by decide +kernel

/-- Three stored rows whose rowid order differs from descending NOCASE key
order. The flag chooses the original scan policy; neither policy uses list order. -/
def scanInput (withoutRowid : Bool) : Table :=
  { shape := {
      columns := [{ name := name! "id", declaredType := some "INTEGER" },
        { name := name! "email", declaredType := none, collation := .nocase }]
      primaryKey := if withoutRowid then [1] else [0]
      primaryKeyDescending := true
      rowidAlias := if withoutRowid then none else some 0
      withoutRowid }
    rows := [{ rowid := 20, values := [.integer 20, .text (bytes! "a")] },
      { rowid := 30, values := [.integer 30, .text (bytes! "c")] },
      { rowid := 10, values := [.integer 10, .text (bytes! "B")] }] }

/-- Under either scan policy, the actual UPDATE preserves the original scan
order and appends each row's lowercase cell. Proof sketch: discharge wide-row,
alias and key-position premises from the concrete nonempty schema. -/
theorem scan_transport (withoutRowid : Bool) :
    sourceRows (LiteralData.updated (EvalContext.plain 0)
      ((scanInput withoutRowid).appendColumns [(lowered, .null)])
      [(2, .scalar .lower (.cons (.column 1) .nil))] none) =
      (sourceRows (scanInput withoutRowid)).map fun row =>
        row ++ [mapText lowerByte (row.getD 1 .null)] := by
  apply sourceRows_updated_lower (EvalContext.plain 0) (scanInput withoutRowid) lowered 1
  · simp [Table.RowsWide, scanInput]
  · cases withoutRowid <;> simp [Table.RowsAliased, Row.Aliased, scanInput]
  · simp [scanInput]
  · cases withoutRowid <;> simp [scanInput]
  · simp [scanInput]
  · rfl
  · rfl

/-- The two policies actually produce different ID sequences: rowids ascending
versus email keys descending under NOCASE. Proof sketch: kernel evaluation of
the existing scan, followed by its first-cell projection. -/
theorem different_scan_orders :
    ((sourceRows (scanInput false)).map (fun row => row.getD 0 .null),
      (sourceRows (scanInput true)).map (fun row => row.getD 0 .null)) =
      ([.integer 10, .integer 20, .integer 30], [.integer 30, .integer 10, .integer 20]) := by decide +kernel

/-- A physical table with one storage slot, before its lowercase field is added. -/
def initial (value : Value) : Belay.Sqlite.Model.Database :=
  { catalog := [{ name := name! "customers", entry := .table (input value).shape }]
    rows := [(input value).rows] }

/-- The real ADD COLUMN database operation supplies NULL in the appended field. -/
def extended (value : Value) : Belay.Sqlite.Model.Database :=
  (initial value).addColumn 0 lowered .null

/-- The resolved plain backfill, without a foreign-key or trigger program. -/
def backfill : Statement :=
  .update 0 [(2, .scalar .lower (.cons (.column 1) .nil))] none [] [] none

/-- The actual statement effect succeeds on a nonempty table and stores the
lowercase cell. Proof sketch: kernel evaluation of the real UPDATE effect. -/
theorem backfill_effect_nonempty :
    (runStatement 0 {} [] backfill (extended (.text (bytes! "ALPHA")))).effect =
      .ok ((extended (.text (bytes! "ALPHA"))).setRows 0
        [{ rowid := 1, values := [.integer 1, .text (bytes! "ALPHA"), .text (bytes! "alpha")] }]) := by decide +kernel

/-- For every source Value and every successful real backfill effect, the stored
table contains its original cells and computed lowercase cell. The result is
derived from the effect rather than assumed as a row relation. Proof sketch:
the exact effect law applies to the table supplied by the ADD COLUMN operation. -/
theorem stored_table_for_every_value (value : Value) (after : Belay.Sqlite.Model.Database)
    (success : (runStatement 0 {} [] backfill (extended value)).effect = .ok after) :
    after.table 0 = some
      { shape := { (input value).shape with columns := (input value).shape.columns ++ [lowered] }
        rows := [{ rowid := 1, values := [.integer 1, value, mapText lowerByte value] }] } := by
  have stored := table_after_lower_update 0 {} [] (input value) lowered 1
    (Database.table_addColumn lowered .null (by rfl : (initial value).table 0 = some (input value)))
    (by simp [extended, initial, Database.addColumn])
    (by simp [Table.RowsWide, input])
    (by simp [Table.RowsAliased, Row.Aliased, input])
    (by simp [input]) (by simp [input]) rfl rfl success
  simpa [input, Row.appendValues] using stored

#print axioms store_lower
#print axioms comparisonOperands_lower
#print axioms eval_lower
#print axioms generatedCells_plain
#print axioms movedRowid_append
#print axioms assign_lower_append
#print axioms updated_lower_append
#print axioms storedFilter_append
#print axioms originalFilter_append
#print axioms results_translate
#print axioms results_preserve
#print axioms backfill_for_every_value
#print axioms lookup_for_every_parameter
#print axioms five_value_kinds
#print axioms sourceRows_updated_lower
#print axioms scan_transport
#print axioms different_scan_orders
#print axioms runStatement_update_ok
#print axioms table_after_update_ok
#print axioms table_after_lower_update
#print axioms sourceRows_after_lower_update
#print axioms backfill_effect_nonempty
#print axioms stored_table_for_every_value

end NormalizedFieldFixture
