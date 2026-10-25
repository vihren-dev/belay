import CustomerInsertSite

/-! A fixture module of `tests/surface_assertion_examples_test.py`: what the three queries of the insert and
lookup claim say about every database (ADR 0017, S6). Each query is evaluated by the existing laws of the
`SELECT 1` forms, over the rows of the table in any scan order, and the database after the insert keeps the
catalog and has the old rows and the new one. -/

set_option doc.verso true

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- Over every database with a table {lit}`customers` that has the column {lit}`id` at a position: no customer has
the id exactly when the condition {lit}`id = ?1` is false for every row. Proof sketch: apply
{name}`Holds.iff_selectOne_notExists` to the resolved condition. -/
theorem no_customer_has_the_id_iff (db : Database) (id : Int64) (position col : Nat) (table : CatalogTable)
    (cell : CatalogColumn)
    (found : db.raw.catalog.findTable (name! "customers") = some (position, table))
    (column : columnPosition table.columns (name! "id") = some col) (columnAt : table.columns[col]? = some cell) :
    Holds (noCustomerHasTheId id) db ↔
      ∀ row ∈ Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] },
        Resolved.truthy ((equalsParameter cell col 1).eval (Resolved.EvalContext.bound [.integer id.toInt]) row) =
          false := by
  have resolves := FilterResolves.of_term (dqs := runContext.profile.dqsDml)
    (scope := tableScope db.raw.catalog { table := name! "customers", alias := none } position table) (aliases := [])
    (shapes := { current := some 0 })
    (term := .compare .eq (.identifier (name! "id") .none) (.parameter 1)) (by simp [namesAlias])
    (result := (equalsParameter cell col 1, none))
    (by simp [sql_simp, column, columnAt, equalsParameter]; rfl)
  refine Iff.trans (Holds.iff_selectOne_notExists (namedSource := rfl) (head := rfl) (arguments := rfl) found resolves
    ?_) ?_
  · simp [sql_simp, equalsParameter]
  · simp

/-- Over every database with a table {lit}`customers` that has the column {lit}`id`: exactly one customer has the id
exactly when the condition {lit}`id = ?1` is true for one row of the table. Proof sketch: apply
{name}`Holds.iff_selectOne_count` to the resolved conditions. -/
theorem one_customer_has_the_id_iff (db : Database) (id : Int64) (position col : Nat) (table : CatalogTable)
    (cell : CatalogColumn)
    (found : db.raw.catalog.findTable (name! "customers") = some (position, table))
    (column : columnPosition table.columns (name! "id") = some col) (columnAt : table.columns[col]? = some cell) :
    Holds (exactlyOneCustomerHasTheId id) db ↔
      Resolved.countMatching (Resolved.EvalContext.bound [.integer id.toInt]) (some (equalsParameter cell col 1))
        { shape := table, rows := db.raw.rows.getD position [] } = 1 := by
  have mainResolves : ∀ lowest, FilterResolves runContext.profile.dqsDml [] []
      (some (.compare .eq (.subquery 0) (.numeric "1")))
      (some (.compare .eq none (.subquery 0) (.literal (.integer 1)) .binary)) { later := [countShape lowest] } :=
    fun lowest => FilterResolves.of_term (term := .compare .eq (.subquery 0) (.numeric "1"))
      (result := (.compare .eq none (.subquery 0) (.literal (.integer 1)) .binary, none)) (by simp [namesAlias]) (by
      simp [sql_simp, countShape]; rfl)
  have subResolves := FilterResolves.of_term (dqs := runContext.profile.dqsDml)
    (scope := tableScope db.raw.catalog { table := name! "customers", alias := none } position table) (aliases := [])
    (shapes := { current := some 0 })
    (term := .compare .eq (.identifier (name! "id") .none) (.parameter 1)) (by simp [namesAlias])
    (result := (equalsParameter cell col 1, none))
    (by simp [sql_simp, column, columnAt, equalsParameter]; rfl)
  refine Iff.trans (Holds.iff_selectOne_count (namedSource := rfl) (head := rfl) (count := by decide) (arguments := rfl) found subResolves
    mainResolves (by simp [sql_simp]) (by simp [equalsParameter, sql_simp])) ?_
  simp [sql_simp, Resolved.comparisonOperands, Resolved.SubqueryRun.count, Value.isNull, Comparison.holds]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

/-- For every database, id, name, and catalog entry of {lit}`customers` with its first two columns: the
assertion {name}`aCustomerHasTheIdAndName` holds exactly when a scanned row satisfies the id and the name
conditions. Proof sketch: the resolution of the query, then the laws of the row count. -/
theorem a_customer_has_the_id_and_name_iff (db : Database) (id : Int64) (name : String) (position : Nat) (table : CatalogTable)
    (idCell nameCell : CatalogColumn)
    (found : db.raw.catalog.findTable (name! "customers") = some (position, table))
    (idAt : columnPosition table.columns (name! "id") = some 0) (idCellAt : table.columns[0]? = some idCell)
    (nameAt : columnPosition table.columns (name! "name") = some 1) (nameCellAt : table.columns[1]? = some nameCell) :
    Holds (aCustomerHasTheIdAndName id name) db ↔
      ∃ row ∈ Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] },
        Resolved.truthy ((equalsParameter idCell 0 1).eval (Resolved.EvalContext.bound [.integer id.toInt, .text name.toUTF8.toList]) row) = true ∧ 
        Resolved.truthy ((equalsParameter nameCell 1 2).eval (Resolved.EvalContext.bound [.integer id.toInt, .text name.toUTF8.toList]) row) = true := by
  have resolves := FilterResolves.of_term (dqs := runContext.profile.dqsDml)
    (scope := tableScope db.raw.catalog { table := name! "customers", alias := none } position table) (aliases := [])
    (shapes := { later := [] })
    (term := .and (.compare .eq (.identifier (name! "id") .none) (.parameter 1)) (.compare .eq (.identifier (name! "name") .none) (.parameter 2))) (by simp [namesAlias])
    (result := (.and (equalsParameter idCell 0 1) (equalsParameter nameCell 1 2), none))
    (by simp [sql_simp, idAt, nameAt, idCellAt, nameCellAt, equalsParameter]; constructor <;> rfl)
  refine Iff.trans (Holds.iff_selectOne (namedSource := rfl) (head := rfl) (arguments := rfl) found resolves ?_) ?_
  · simp [sql_simp, equalsParameter]
  · simp [sql_simp]

/-- The database with the new row in the table keeps the catalog, so the table is still found. -/
theorem found_after_insert {db : Database} {id : Int64} {name : String} (site : CustomerInsertSite db id name)
    (rows : List Row) :
    (db.raw.setRows site.position rows).catalog.findTable (name! "customers") = some (site.position, site.table) :=
  site.found

/-- The rows of the table after the insert are the old rows and the new one. -/
theorem rows_after_insert {db : Database} {id : Int64} {name : String} (site : CustomerInsertSite db id name)
    (row : Row) :
    (db.raw.setRows site.position (db.raw.rows.getD site.position [] ++ [row])).rows.getD site.position [] =
      db.raw.rows.getD site.position [] ++ [row] :=
  Model.Database.rows_getD_setRows _ (Model.Database.position_lt_rows db.valid.admitted.rowsShaped site.found)

#print axioms no_customer_has_the_id_iff
#print axioms one_customer_has_the_id_iff
#print axioms a_customer_has_the_id_and_name_iff
#print axioms found_after_insert
#print axioms rows_after_insert

end AssertionExamples
