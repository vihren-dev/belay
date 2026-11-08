import SelectOneWhereSupport

/-! A fixture of `tests/surface_claims_test.py`: the query forms `SELECT 1 WHERE [NOT] EXISTS
(SELECT 1 FROM t WHERE p)` over every database, through the phase rules of ADR 0027
(`SelectOneWhereSupport.lean`). Each claim is about every database; each claim has an instance on one
database, where `decide +kernel` checks that its two sides agree, so that no claim is vacuous. -/

set_option doc.verso true

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The guide's first database: table {lit}`invoices` with two open invoices, of 10 and of 0. -/
def shop : Database := db! r"
  CREATE TABLE invoices (
    id INTEGER PRIMARY KEY,
    customer TEXT NOT NULL,
    amount INTEGER NOT NULL CHECK (amount >= 0),
    status TEXT NOT NULL DEFAULT 'open'
  );
  INSERT INTO invoices (id, customer, amount) VALUES (1, 'acme', 10), (2, 'zeta', 0);"

/-- The catalog position and the table of {lit}`invoices` in {name}`shop`. -/
def invoices : Nat × CatalogTable := (shop.raw.catalog.findTable (name! "invoices")).get (by decide +kernel)

example : shop.raw.catalog.findTable (name! "invoices") = some invoices := by decide +kernel

/-- Over every database that has a table {lit}`invoices` with a column {lit}`amount` at position
{lit}`index`, "no invoice has a negative amount" holds exactly when the comparison is true for no row.
Proof sketch: {name}`whereOne_claims` with {name}`resolveStatement_selectOne_notExists`, and
{name}`tableOne_run` for the subquery. -/
theorem no_invoice_is_negative (db : Database) (position index : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable (name! "invoices") = some (position, table))
    (column : columnPosition table.columns (name! "amount") = some index) :
    Holds (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM invoices WHERE amount < 0)") db ↔
      ∀ row ∈ Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] },
        Resolved.truthy (Comparison.lt.apply
          (Resolved.comparisonOperands (comparisonAffinity (table.columns[index]?.map CatalogColumn.affinity) none)
            (row.getD index .null) 0).1
          (Resolved.comparisonOperands (comparisonAffinity (table.columns[index]?.map CatalogColumn.affinity) none)
            (row.getD index .null) 0).2
          ((table.columns[index]?.map (·.collation)).getD .binary)) = false := by
  have resolves := FilterResolves.of_term (dqs := runContext.profile.dqsDml)
    (scope := tableScope db.raw.catalog { table := name! "invoices", alias := none } position table) (aliases := [])
    (shapes := { current := some 0 })
    (term := .compare .lt (.identifier (name! "amount") .none) (.numeric "0")) (by simp [namesAlias])
    (result := (.compare .lt (comparisonAffinity (table.columns[index]?.map CatalogColumn.affinity) none) (.column index)
      (.literal (.integer 0)) ((table.columns[index]?.map (·.collation)).getD .binary), none))
    (by simp [sql_simp, column])
  have calm : ∀ expression ∈ (some (.compare .lt (comparisonAffinity (table.columns[index]?.map CatalogColumn.affinity)
      none) (.column index) (.literal (.integer 0)) ((table.columns[index]?.map (·.collation)).getD .binary)) :
      Option Resolved.Expr).toList, expression.Calm := by simp [sql_simp]
  have run := tableOne_run db [] (name! "invoices") position table _ found calm
  have claims := whereOne_claims
    (script := sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM invoices WHERE amount < 0)") (isQuery := rfl)
    _ [] rfl db (.not (.exists 0)) _
    (resolveStatement_selectOne_notExists runContext _ _ _ position table _ rfl rfl rfl found resolves)
    (Resolved.Statement.Calm.selectOne_subquery position _ _ _ _ ((Resolved.Expr.calm_not _).2 (Resolved.Expr.calm_exists _))
      calm (Resolved.Expr.calm_literal _))
    (by rw [Resolved.Expr.fault_not, Resolved.Expr.fault_exists, Resolved.EvalContext.statement_one]; exact run.1)
  rw [claims.1, Resolved.Expr.eval_not, Resolved.truthy_not, Resolved.Expr.eval_exists,
    Resolved.EvalContext.statement_one, run.2]
  simp [someRow, sql_simp, Resolved.falsy]; exact Iff.rfl

/-- Over every database with a table of invoices, EXISTS holds exactly when the table has a source
row, is empty exactly when it has none, and never fails. Proof sketch: {name}`whereOne_claims` with
{name}`resolveStatement_selectOne_exists` and the absent filter. -/
theorem exists_invoice_observations (db : Database) (position : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable (name! "invoices") = some (position, table)) :
    (Holds (sql r"SELECT 1 WHERE EXISTS (SELECT 1 FROM invoices)") db ↔
      ∃ row ∈ Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }, True) ∧
    (Empty (sql r"SELECT 1 WHERE EXISTS (SELECT 1 FROM invoices)") db ↔
      ∀ row ∈ Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }, False) ∧
    ¬ Fails (sql r"SELECT 1 WHERE EXISTS (SELECT 1 FROM invoices)") db := by
  have resolves : FilterResolves runContext.profile.dqsDml
      (tableScope db.raw.catalog { table := name! "invoices", alias := none } position table) [] none none { current := some 0 } :=
    .inl ⟨rfl, rfl⟩
  have run := tableOne_run db [] (name! "invoices") position table none found (by simp)
  obtain ⟨holds, empty, notFails⟩ := whereOne_claims
    (script := sql r"SELECT 1 WHERE EXISTS (SELECT 1 FROM invoices)") (isQuery := rfl) _ [] rfl db (.exists 0) _
    (resolveStatement_selectOne_exists runContext _ _ _ position table _ rfl rfl rfl found resolves)
    (Resolved.Statement.Calm.selectOne_subquery position _ _ _ _ (Resolved.Expr.calm_exists _) (by simp)
      (Resolved.Expr.calm_literal _))
    (by rw [Resolved.Expr.fault_exists, Resolved.EvalContext.statement_one]; exact run.1)
  rw [holds, empty, Resolved.Expr.eval_exists, Resolved.EvalContext.statement_one, run.2]
  refine ⟨?_, ?_, notFails⟩ <;> simp [someRow, List.any_eq_true, List.any_eq_false]

/-- Over every database with a table of invoices, NOT EXISTS reverses the row and empty
observations of EXISTS, and never fails. Proof sketch: as {name}`exists_invoice_observations`, with
{name}`resolveStatement_selectOne_notExists`. -/
theorem not_exists_invoice_observations (db : Database) (position : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable (name! "invoices") = some (position, table)) :
    (Holds (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM invoices)") db ↔
      ∀ row ∈ Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }, False) ∧
    (Empty (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM invoices)") db ↔
      ∃ row ∈ Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }, True) ∧
    ¬ Fails (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM invoices)") db := by
  have resolves : FilterResolves runContext.profile.dqsDml
      (tableScope db.raw.catalog { table := name! "invoices", alias := none } position table) [] none none { current := some 0 } :=
    .inl ⟨rfl, rfl⟩
  have run := tableOne_run db [] (name! "invoices") position table none found (by simp)
  obtain ⟨holds, empty, notFails⟩ := whereOne_claims
    (script := sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM invoices)") (isQuery := rfl) _ [] rfl db (.not (.exists 0)) _
    (resolveStatement_selectOne_notExists runContext _ _ _ position table _ rfl rfl rfl found resolves)
    (Resolved.Statement.Calm.selectOne_subquery position _ _ _ _ ((Resolved.Expr.calm_not _).2 (Resolved.Expr.calm_exists _))
      (by simp) (Resolved.Expr.calm_literal _))
    (by rw [Resolved.Expr.fault_not, Resolved.Expr.fault_exists, Resolved.EvalContext.statement_one]; exact run.1)
  rw [holds, empty, Resolved.Expr.eval_not, Resolved.truthy_not, Resolved.Expr.eval_exists,
    Resolved.EvalContext.statement_one, run.2]
  refine ⟨?_, ?_, notFails⟩ <;> simp [someRow, Resolved.falsy, List.any_eq_true, List.any_eq_false]

/-- An existing table without invoices distinguishes an empty result from a missing-table error. -/
def noInvoices : Database := db! r"CREATE TABLE invoices (amount INTEGER);"

/-- The existing empty table of invoices. -/
def emptyInvoices : CatalogTable := (noInvoices.raw.catalog.findTable (name! "invoices")).get (by decide +kernel) |>.2

example : Holds (sql r"SELECT 1 WHERE EXISTS (SELECT 1 FROM invoices)") shop :=
  (exists_invoice_observations shop invoices.1 invoices.2 (by decide +kernel)).1.2 (by decide +kernel)
example : ¬ Holds (sql r"SELECT 1 WHERE EXISTS (SELECT 1 FROM invoices)") noInvoices := by
  rw [(exists_invoice_observations noInvoices 0 emptyInvoices (by decide +kernel)).1]
  decide +kernel
example : Empty (sql r"SELECT 1 WHERE EXISTS (SELECT 1 FROM invoices)") noInvoices :=
  (exists_invoice_observations noInvoices 0 emptyInvoices (by decide +kernel)).2.1.2 (by decide +kernel)
example : ¬ Empty (sql r"SELECT 1 WHERE EXISTS (SELECT 1 FROM invoices)") shop := by
  rw [(exists_invoice_observations shop invoices.1 invoices.2 (by decide +kernel)).2.1]
  decide +kernel
example : ¬ Fails (sql r"SELECT 1 WHERE EXISTS (SELECT 1 FROM invoices)") shop :=
  (exists_invoice_observations shop invoices.1 invoices.2 (by decide +kernel)).2.2
example : Holds (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM invoices)") noInvoices :=
  (not_exists_invoice_observations noInvoices 0 emptyInvoices (by decide +kernel)).1.2 (by decide +kernel)
example : ¬ Holds (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM invoices)") shop := by
  rw [(not_exists_invoice_observations shop invoices.1 invoices.2 (by decide +kernel)).1]
  decide +kernel
example : Empty (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM invoices)") shop :=
  (not_exists_invoice_observations shop invoices.1 invoices.2 (by decide +kernel)).2.1.2 (by decide +kernel)
example : ¬ Empty (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM invoices)") noInvoices := by
  rw [(not_exists_invoice_observations noInvoices 0 emptyInvoices (by decide +kernel)).2.1]
  decide +kernel
example : ¬ Fails (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM invoices)") noInvoices :=
  (not_exists_invoice_observations noInvoices 0 emptyInvoices (by decide +kernel)).2.2

#print axioms no_invoice_is_negative
#print axioms exists_invoice_observations
#print axioms not_exists_invoice_observations
