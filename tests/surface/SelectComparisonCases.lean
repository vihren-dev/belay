import SelectProjectionCases

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A03 of the filter rules of ADR 0027: {lit}`WHERE amount > :minimum` gives each
returned row the comparison of the model with the bound minimum, over every database with generic
table and column premises and for every value of the parameter, with the NULL, affinity and
parameter type contrasts. The claim is the comparison of the model, not an order of Lean numbers:
the contrasts show where the two differ. -/

namespace SelectComparisonCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectProjectionCases

/-- The query of A03: the amounts above a minimum. -/
def above (minimum : Value) : Script := sql r"SELECT amount FROM invoices WHERE amount > :minimum" minimum

/-- The query of A03 has one statement. -/
theorem above_one (minimum : Value) : (above minimum).statements.length = 1 := rfl

/-- A row is one value above the bound minimum under the comparison of the model: the value and the minimum
are not NULL, and the operands after the affinity compare as greater under the collation. -/
def aboveMinimum (affinity : Option Affinity) (collation : Collation) (minimum : Value) (row : List Value) : Prop :=
  ∃ amount, row = [amount] ∧ amount.isNull = false ∧ minimum.isNull = false ∧
    Comparison.gt.holds (collation.compare (Resolved.comparisonOperands affinity amount minimum).1
      (Resolved.comparisonOperands affinity amount minimum).2) = true

/-- A03 with generic premises: for every database, environment and value {lit}`minimum`, when the
catalog has a table {lit}`invoices` at a position with a column {lit}`amount`, the query of the
amounts above the minimum returns a result, and each of its rows is one value that is above the
bound minimum ({name}`boundValue`) as {name}`aboveMinimum` says, with the affinity and the collation
of the column. The column can have any type, and the table any rows, also none. Proof sketch: the
resolution laws give the simple query of the table; {name}`Run.query_returnsResult_calmTable` reduces
the claim to the possible results over the scan; {name}`Resolved.Query.mem_possibleResults_plain`
gives the source row of each result row, where the condition is true, and
{name}`Resolved.ordinary_of_truthy` reads the comparison from it. -/
theorem amounts_above (db : Database) (env : Env) (minimum : Value) {position amountIndex : Nat}
    {table : CatalogTable} {amount : CatalogColumn}
    (found : db.raw.catalog.findTable (name! "invoices") = some (position, table))
    (amountFound : columnPosition table.columns (name! "amount") = some amountIndex)
    (amountAt : table.columns[amountIndex]? = some amount) :
    (db.run (query (above minimum) (above_one minimum)) env).returnsRows
      (aboveMinimum (some amount.affinity) amount.collation (boundValue minimum)) := by
  have resolves := FilterResolves.of_term (dqs := runContext.profile.dqsDml)
    (scope := tableScope db.raw.catalog { table := name! "invoices", alias := none } position table) (aliases := [])
    (shapes := { later := [] })
    (term := .compare .gt (.identifier (name! "amount") .none) (.parameter 1)) (by simp [namesAlias])
    (by simp [resolveOperand_compare_of_notBoolean _ (Syntax.Expr.parameter 1) rfl, resolveOperand_identifier_table amountFound,
      resolveOperand_parameter]; rfl)
  obtain ⟨names, resolved⟩ := resolveStatement_select_column runContext (db.raw.connection env.counters).resolveState
    { table := name! "invoices", alias := none } _ position table _ (name! "amount") "amount" rfl rfl rfl found
    amountFound resolves
  rw [Run.returnsRows, Run.query_returnsResult_calmTable (script := above minimum) rfl (above_one minimum) db env
    resolved rfl (Database.table_of_findTable _ _ _ _ found) ?calm rfl rfl rfl ?noOverflow rfl]
  · intro result member row inResult
    obtain ⟨source, -, kept, rfl⟩ := Resolved.Query.mem_possibleResults_plain rfl rfl rfl member inResult
    have collation : comparisonCollation (tableScope db.raw.catalog { table := name! "invoices", alias := none } position
        table) (.identifier (name! "amount") .none) (.parameter 1) = amount.collation := by
      simp only [comparisonCollation, Syntax.Expr.explicitCollation, Syntax.Expr.columnCollation, tableScope,
        resolveName_one_source_at amountFound]
      simp [Scope.columns, Scope.singleAt, amountAt]
    simp only [Resolved.Query.simple, Option.all_some, Resolved.Expr.eval_compare, Resolved.Expr.eval_column,
      Resolved.Expr.eval_parameter, amountAt, Option.map_some, comparisonAffinity, collation, List.headD_cons,
      parameterValue, Nat.sub_self, List.getD_cons_zero] at kept
    obtain ⟨present, bound, holds⟩ := Resolved.ordinary_of_truthy (by decide) (by decide) kept
    exact ⟨_, by simp [Resolved.Query.rowOutput, Resolved.Query.simple, Resolved.Expr.eval_column], present, bound,
      holds⟩
  · refine Resolved.Statement.simpleColumn_calm _ _ _ _ fun expression member => ?_
    simp only [Option.toList_some, List.mem_singleton] at member
    subst member
    exact (Resolved.Expr.calm_compare ..).mpr ⟨Resolved.Expr.calm_column _, Resolved.Expr.calm_parameter _⟩
  · simp [Resolved.Query.fails, Resolved.Query.simple]

/-- The guide's invoices with two amounts, 10 and 0, in a column of INTEGER affinity. -/
def typed : Database := shop

/-- The same amounts in a column without a type, which has BLOB affinity. -/
def untyped : Database := db! r"
  CREATE TABLE invoices (id INTEGER PRIMARY KEY, amount);
  INSERT INTO invoices VALUES (1, 10), (2, 0);"

/-- The text {lit}`'5'`. -/
def five : Value := .text "5".toUTF8.toList

/-- A03 witness: with the integer minimum 5, the query returns the amount 10. -/
theorem integer_witness : (typed.run (query (above (.integer 5)) (above_one _))).returnsResult (· = [[.integer 10]]) := by
  decide +kernel

/-- A03 NULL contrast: with a NULL minimum, or a NaN REAL that binds as NULL, no amount is above it, and
the result is empty. -/
theorem null_contrast :
    (typed.run (query (above .null) (above_one _))).returnsResult (· = []) ∧
      (typed.run (query (above (.real (0.0 / 0.0 : Float).toBits)) (above_one _))).returnsResult (· = []) :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- A03 affinity contrast: the text minimum {lit}`'5'` compares as the number 5 with a column of
INTEGER affinity, so 10 is above it; with a column of BLOB affinity it stays text, which is greater
than every number, so no amount is above it. -/
theorem affinity_contrast :
    (typed.run (query (above five) (above_one _))).returnsResult (· = [[.integer 10]]) ∧
      (untyped.run (query (above five) (above_one _))).returnsResult (· = []) :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- A03 parameter type contrast: with the REAL minimum 9.5 the query returns the amount 10, and with
the text {lit}`'abc'`, which is no number, it returns no amount, also under INTEGER affinity. -/
theorem parameter_type_contrast :
    (typed.run (query (above (.real (9.5 : Float).toBits)) (above_one _))).returnsResult (· = [[.integer 10]]) ∧
      (typed.run (query (above (.text "abc".toUTF8.toList)) (above_one _))).returnsResult (· = []) :=
  ⟨by decide +kernel, by decide +kernel⟩

#print axioms amounts_above
#print axioms integer_witness
#print axioms null_contrast
#print axioms affinity_contrast
#print axioms parameter_type_contrast

end SelectComparisonCases
