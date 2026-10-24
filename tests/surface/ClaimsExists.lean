import Belay

/-! A fixture of `tests/surface_claims_test.py`: the query forms `SELECT 1 WHERE [NOT] EXISTS
(SELECT 1 FROM t WHERE p)` over every database (ADR 0017, S4; `Belay/Sqlite/ExistsQuery.lean`).
Each claim is about every database; each claim has an instance on one database, where
`decide +kernel` checks that its two sides agree, so that no claim is vacuous. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The guide's first database: table `invoices` with two open invoices, of 10 and of 0. -/
def shop : Database := db! r"
  CREATE TABLE invoices (
    id INTEGER PRIMARY KEY,
    customer TEXT NOT NULL,
    amount INTEGER NOT NULL CHECK (amount >= 0),
    status TEXT NOT NULL DEFAULT 'open'
  );
  INSERT INTO invoices (id, customer, amount) VALUES (1, 'acme', 10), (2, 'zeta', 0);"

/-- The catalog position and the table of `invoices` in `shop`. -/
def invoices : Nat × CatalogTable := (shop.raw.catalog.findTable (name! "invoices")).get (by decide +kernel)

example : shop.raw.catalog.findTable (name! "invoices") = some invoices := by decide +kernel

/-- Over every database that has a table `invoices` with a column `amount` at position `index`,
"no invoice has a negative amount" holds exactly when the comparison is true for no row. -/
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
    (scope := tableScope db.raw.catalog ⟨name! "invoices", none, none⟩ position table) (aliases := [])
    (shapes := { current := some 0 })
    (term := .compare .lt (.identifier (name! "amount") .none) (.numeric "0")) (by simp [namesAlias])
    (by simp [sql_simp, column]; rfl)
  refine Iff.trans (Holds.iff_selectOne_notExists (head := rfl) (arguments := rfl) found resolves ?_) ?_
  · simp [sql_simp]
  · simp [sql_simp]; exact Iff.rfl

-- The instance on `shop`: no invoice is negative, and both sides agree.
example : Holds (sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM invoices WHERE amount < 0)") shop :=
  (no_invoice_is_negative shop invoices.1 2 invoices.2 (by decide +kernel) (by decide +kernel)).2
    (by decide +kernel)
