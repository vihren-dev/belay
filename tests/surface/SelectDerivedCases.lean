import SelectDerivedSupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A17 of ADR 0027: a derived table, a common table expression and a view over
{lit}`SELECT customer_id, amount FROM orders WHERE amount > 5` return the {lit}`customer_id` of
each big order, through one specification of the inner query ({lit}`big_run`). The contrasts
show that a column of a derived table does not keep the constraints of its source column, and that
the model describes no result over a derived table whose rows its window does not fix. -/

namespace SelectDerivedCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases (cell)
open SelectJoinCases (shop orderRows shop_found partial_)

/-- The catalog of {name}`shop` with the view {lit}`big` of the big orders. -/
def shopView : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT NOT NULL);
  CREATE TABLE orders (id INTEGER PRIMARY KEY, customer_id INTEGER, amount INTEGER NOT NULL);
  CREATE VIEW big AS SELECT customer_id, amount FROM orders WHERE amount > 5;"

/-- The query of A17 over a derived table. -/
def derivedScript : Script :=
  sql r"SELECT x.customer_id FROM (SELECT customer_id, amount FROM orders WHERE amount > 5) x"

/-- The query of A17 over a common table expression. -/
def cteScript : Script :=
  sql r"WITH big AS (SELECT customer_id, amount FROM orders WHERE amount > 5) SELECT customer_id FROM big"

/-- The query of A17 over the view of {name}`shopView`. -/
def viewScript : Script := sql r"SELECT customer_id FROM big"

/-- The {lit}`customer_id` of each {name}`Big` order, in scan order. -/
def bigCustomers (db : Database) : List (List Value) := ((orderRows db).filter Big).map fun order => [cell 1 order]

/-- For every database and every result that is a permutation of the first cell of each row of
{name}`bigRows`, the result is a permutation of the {name}`bigCustomers`. -/
theorem perm_bigCustomers (db : Database) {result : List (List Value)}
    (perm : result.Perm ((bigRows db).map fun row => [cell 0 row])) : result.Perm (bigCustomers db) := by
  simpa [bigRows, bigCustomers, Function.comp_def, Resolved.Expr.eval_column] using perm

/-- A17 with a derived table: for every database with the catalog of {name}`shop` and every
environment, {name}`derivedScript` returns a result that is a permutation of the
{name}`bigCustomers`. Proof sketch: {name}`derived_returns` with the inner rule {name}`big_run`. -/
theorem derived_big (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (db.run (query derivedScript rfl) env).returnsResult fun result => result.Perm (bigCustomers db) :=
  have run := big_run db (Database.table_of_findTable db.raw _ _ _ (shop_found db schema).2)
  derived_returns shop bigQuery derivedScript rfl _ rfl (by decide +kernel)
    (by unfold Resolved.Statement.Calm; decide +kernel) db env schema _ run.1 run.2.1 run.2.2.1 run.2.2.2 _
    fun _ perm => perm_bigCustomers db perm

/-- A17 with a common table expression: for every database with the catalog of {name}`shop` and
every environment, {name}`cteScript` returns a result that is a permutation of the
{name}`bigCustomers`. Proof sketch: as {name}`derived_big`; the expression resolves to the same
query. -/
theorem cte_big (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (db.run (query cteScript rfl) env).returnsResult fun result => result.Perm (bigCustomers db) :=
  have run := big_run db (Database.table_of_findTable db.raw _ _ _ (shop_found db schema).2)
  derived_returns shop bigQuery cteScript rfl _ rfl (by decide +kernel)
    (by unfold Resolved.Statement.Calm; decide +kernel) db env schema _ run.1 run.2.1 run.2.2.1 run.2.2.2 _
    fun _ perm => perm_bigCustomers db perm

/-- A17 with a view: for every database with the catalog of {name}`shopView` and every
environment, {name}`viewScript` returns a result that is a permutation of the
{name}`bigCustomers`. Proof sketch: as {name}`derived_big`; the view resolves to the same query,
and the catalog has {lit}`orders` at position 1. -/
theorem view_big (db : Database) (env : Env) (schema : db.HasCatalog shopView) :
    (db.run (query viewScript rfl) env).returnsResult fun result => result.Perm (bigCustomers db) :=
  have orders : db.raw.catalog.findTable (name! "orders") = some (1, SelectJoinCases.ordersShape) := by
    rw [show db.raw.catalog = shopView.raw.catalog from schema]
    decide +kernel
  have run := big_run db (Database.table_of_findTable db.raw _ _ _ orders)
  derived_returns shopView bigQuery viewScript rfl _ rfl (by decide +kernel)
    (by unfold Resolved.Statement.Calm; decide +kernel) db env schema _ run.1 run.2.1 run.2.2.1 run.2.2.2 _
    fun _ perm => perm_bigCustomers db perm

/-- A17 contrast: on {name}`partial_` the derived table gives the {lit}`customer_id` 1 and NULL of
the orders with the amounts 10 and 7. Native SQLite 3.51.0 gives the same rows. -/
example : (partial_.run (query derivedScript rfl)).returnsResult (·.Perm [[.integer 1], [.null]]) := by
  decide +kernel

/-- A17 contrast, constraints: the column {lit}`amount` of {lit}`orders` is NOT NULL, but the
column of a derived table over a left join is NULL for {lit}`zeta`, which has no order. A proof
about the derived column cannot use the constraint of its source column. Native SQLite 3.51.0 gives
the rows 10 and NULL. -/
example : (partial_.run (query (sql r"SELECT x.amount FROM (SELECT o.amount FROM customers c
    LEFT JOIN orders o ON o.customer_id = c.id) x") rfl)).returnsResult (·.Perm [[.integer 10], [.null]]) := by
  decide +kernel

/-- A17 contrast, certainty: the derived table {lit}`SELECT customer_id FROM orders LIMIT 1` can
give the {lit}`customer_id` of any order, because it has no {lit}`ORDER BY`. The model describes no
result of the outer query ({name}`Resolved.Query.source_derived_uncertain`), where native SQLite
3.51.0 gives 1 with a full scan. -/
example : ¬ (partial_.run (query (sql r"SELECT x.customer_id FROM (SELECT customer_id FROM orders LIMIT 1) x")
    rfl)).returnsResult (fun _ => True) := by
  decide +kernel

#print axioms perm_bigCustomers
#print axioms derived_big
#print axioms cte_big
#print axioms view_big

end SelectDerivedCases
