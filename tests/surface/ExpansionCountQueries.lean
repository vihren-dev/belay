import Belay

/-! A fixture module of `tests/surface_assertion_examples_test.py`: what the guide's count query says about every
database (ADR 0017, S6). The query `SELECT 1 WHERE (SELECT count(*) FROM customers) = $n` holds exactly when the
table has `n` rows, whatever the other columns, rows and objects of the database are. -/

set_option doc.verso true

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The guide's count claim, for a number: the table of customers has that many rows. -/
def customerCountIs (n : Int64) : Script :=
  sql r"SELECT 1 WHERE (SELECT count(*) FROM customers) = $n"

/-- Over every database with a table {lit}`customers` at a position: the count query holds exactly when the
stored rows of the table number {lit}`n`. Proof sketch: apply {name}`Script.outputOn_count` to the
resolved comparison of the subquery with the parameter; the count of a table without a condition is its
number of rows ({name}`Resolved.countMatching_none`). -/
theorem customer_count_is_iff (db : Database) (n : Int64) (position : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable (name! "customers") = some (position, table)) :
    Holds (customerCountIs n) db ↔ (db.raw.rows.getD position []).length = n.toInt := by
  have mainResolves : ∀ lowest, FilterResolves runContext.profile.dqsDml [] []
      (some (.compare .eq (.subquery 0) (.parameter 1)))
      (some (.compare .eq none (.subquery 0) (.parameter 1) .binary)) { later := [countShape lowest] } :=
    fun lowest => FilterResolves.of_term (term := .compare .eq (.subquery 0) (.parameter 1))
      (result := (.compare .eq none (.subquery 0) (.parameter 1) .binary, none)) (by simp [namesAlias]) (by
      simp [sql_simp, countShape]; rfl)
  rw [Holds, Script.outputOn_count (script := (customerCountIs n)) (namedSource := rfl) (current := rfl) (head := rfl) (count := by decide)
    (arguments := rfl) found (FilterResolves.of_none _ _ _ _) mainResolves (by simp [sql_simp]) (by simp)]
  simp only [Option.any_some, Output.hasRows, apply_ite]
  simp [sql_simp, Resolved.comparisonOperands, Resolved.SubqueryRun.count, Resolved.countMatching_none,
    Value.isNull, Comparison.holds, boundValue]

#print axioms customer_count_is_iff

end AssertionExamples
