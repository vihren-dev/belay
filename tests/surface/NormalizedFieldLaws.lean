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

end NormalizedFieldFixture
