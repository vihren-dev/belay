import Belay

/-! Public SQL and database quotations for derived-table queries (ADR 0019, D5).
The predicates are checked by the kernel after SQL translation; no native result is embedded
in the library. The final checks ensure uncertain membership has no claimed outcome. -/

open Belay.Sqlite

/-- Two values with TEXT affinity and NOCASE collation. -/
def sourceRows : Database := db! r"
  CREATE TABLE t (x TEXT COLLATE NOCASE);
  INSERT INTO t VALUES ('a'), ('b');"

/-- A derived-column comparison retains the source column's collation. -/
example : Holds (sql r"SELECT 1 FROM (SELECT x FROM t) AS d WHERE d.x = 'A'") sourceRows := by decide +kernel

/-- A compound source supplies all columns to the outer query. -/
example : Holds (sql r"SELECT 1 FROM (SELECT 1 AS x, 2 AS y UNION ALL SELECT 3, 4) WHERE y = 4") sourceRows := by
  decide +kernel

/-- A derived source may read a permitted enclosing query's column. -/
example : Holds (sql r"SELECT 1 FROM t WHERE (SELECT x FROM (SELECT t.x AS x)) = 'a'") sourceRows := by
  decide +kernel

/-- LIMIT zero yields an empty derived source. -/
example : Empty (sql r"SELECT 1 FROM (SELECT x FROM t LIMIT 0)") sourceRows := by decide +kernel

/-- Referencing a sibling table inside a derived source is a prepare error. -/
example : Fails (sql r"SELECT 1 FROM t, (SELECT t.x)") sourceRows := by decide +kernel

/-- A LIMIT whose membership depends on the plan is not a successful query claim. -/
example : ¬ Holds (sql r"SELECT 1 FROM (SELECT x FROM t LIMIT 1)") sourceRows := by decide +kernel

/-- The same uncertain source is not an empty query claim. -/
example : ¬ Empty (sql r"SELECT 1 FROM (SELECT x FROM t LIMIT 1)") sourceRows := by decide +kernel

/-- The same uncertain source is not a failure claim. -/
example : ¬ Fails (sql r"SELECT 1 FROM (SELECT x FROM t LIMIT 1)") sourceRows := by decide +kernel

open Belay.Sqlite.Model

/-- The named-table source law holds for every source callback and a nested-query prefix. -/
example (catalog : Catalog) (position : Nat) (table : CatalogTable)
    (found : catalog.findTable (name! "ledger") = some (position, table))
    (queries : Nat → Except SourceIssue ScopeSource) :
    resolveSources catalog (some {table := name! "ledger", alias := none}) [] 0 queries [8, 0] =
      .ok ([{item := .table position, kind := .inner, condition := .none}],
        tableScope catalog {table := name! "ledger", alias := none} position table) :=
  resolveSources_table catalog _ position table rfl rfl found queries [8, 0]

/-- The pragma source law preserves its rows for every callback and a nested-query prefix. -/
example (catalog : Catalog) (rows : List (List Value))
    (notTable : catalog.findTable (name! "pragma_table_info") = none)
    (notView : catalog.findView (name! "pragma_table_info") = none)
    (info : catalog.tableInfoRows (name! "ledger") = some rows)
    (queries : Nat → Except SourceIssue ScopeSource) :
    let reference : Syntax.TableReference := {
      table := name! "pragma_table_info", alias := none, arguments := some [.string (bytes! "ledger")] }
    resolveSources catalog (some reference) [] 0 queries [8, 2] =
      .ok ([{ item := .pragma (pragmaSource reference (bytes! "ledger") tableInfoNames rows).1,
              kind := .inner, condition := .none }], tableInfoScope reference (bytes! "ledger") rows) := by
  exact resolveSources_tableInfo catalog _ (bytes! "ledger") rows rfl rfl (by decide) notTable notView info queries [8, 2]
