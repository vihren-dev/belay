import Belay

/-! Manually supplied view definitions exercise the catalog boundary before SQL view
DDL is enabled. Uses resolve the stored SELECT; a write, an index, an added column or a trigger
on a view is a prepare error, and a table-valued metadata function stays unmodeled. -/

set_option doc.verso true
set_option maxRecDepth 4000

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

namespace ViewCatalogExamples

/-- A late-bound view whose table does not exist. The catalog stores the written name. -/
def late : CatalogView := {
  columns := some [name! "x"]
  query := { commonTablePlaceholder with
    columns := [.star]
    source := some { table := name! "future", alias := none } } }

/-- A valid database with an unresolved view and no stored view rows. -/
def database : Database := ⟨(Catalog.createView [] (name! "v") late).emptyDatabase, by decide +kernel⟩

/-- View lookup uses the same ASCII-folded namespace as physical table lookup. -/
example : database.catalog.findView (name! "V") = some (0, late) := by decide +kernel

/-- A named view is not a physical table. -/
example : database.catalog.findTable (name! "v") = none := by decide +kernel

/-- Views do not have table rows even when their bodies contain SELECTs. -/
example : database.raw.table 0 = none := by decide +kernel

/-- Nonempty stored rows at a view position violate the existing row-shape atom. -/
example : ¬ ({ database.raw with rows := [[{ rowid := 1, values := [.integer 2] }]] }).RowsShaped := by
  decide +kernel

/-- Removing an earlier object keeps the unresolved definition, without stale positions. -/
example : (Catalog.drop ([{
    name := name! "t"
    entry := .table {columns := [{name := name! "x", declaredType := none}]} }] ++ database.catalog) [0]).findView
    (name! "v") = some (0, late) := by decide +kernel

/-- Dropping the view itself yields the empty valid catalog. -/
example : (database.catalog.drop [0]).Valid Profile.pinned.limits := by decide +kernel

/-- A view reserves its name against CREATE TABLE, with the view-specific message. -/
example : resolveCreateTable runContext database.catalog (name! "v")
    [{name := name! "x", declaredType := none, constraints := []}] [] =
      .ok (.prepareError (.viewExists (name! "v")), database.catalog) := by decide +kernel

/-- An index on a physical table cannot reuse a view's name. -/
example : let catalog := database.catalog.createTable (name! "t") {columns := [{name := name! "x", declaredType := none}]}
    resolveCreateIndex runContext catalog (name! "v") false (name! "t")
      [⟨.identifier (name! "x") .none, false⟩] none =
      .ok (.prepareError (.tableNameUsed (name! "v")), catalog) := by decide +kernel

/-- A foreign key naming a view is a mismatch, even when the view's body has a missing source. -/
example : database.catalog.parentLink {
    table := name! "v", columns := [0], referenced := [], onDelete := .noAction, onUpdate := .noAction} =
    .mismatch 0 := by decide +kernel

/-- Every statement listed here is a write or schema change of a view. -/
def deferred : List Syntax.Statement := [
  .insert (name! "v") none [[.numeric "1"]] [],
  .insert (name! "v") none [[.numeric "1"]] [] (subqueries := [late.query]),
  .update (name! "v") [(name! "x", .numeric "1")] none,
  .delete (name! "v") none,
  .createIndex (name! "i") false (name! "v") [⟨.identifier (name! "x") .none, false⟩] none,
  .addColumn (name! "v") {name := name! "y", declaredType := none, constraints := []},
  .createTrigger (name! "tr") false .before .insert (name! "v") none [] ]

/-- Each of them is a prepare error: a write reads the view's query first, which names the missing
table, and the others refuse the view without reading it. -/
example : deferred.all (fun statement => match resolveStatement runContext
    {catalog := database.catalog} statement with
      | .ok (.prepareError _, _) => true
      | .error _ | .ok (.createTable .., _) | .ok (.createView .., _) | .ok (.createIndex .., _)
      | .ok (.createTrigger .., _) | .ok (.addColumn .., _) | .ok (.drop .., _) | .ok (.begin, _)
      | .ok (.commit, _) | .ok (.rollback, _) | .ok (.insert .., _) | .ok (.insertSelect .., _) | .ok (.update .., _)
      | .ok (.upsert .., _) | .ok (.delete .., _) | .ok (.query .., _) | .ok (.setting .., _) => false)
      = true := by
  decide +kernel

/-- {lit}`PRAGMA table_info` of a view expands its query, so it is no longer a restriction. -/
example : (match resolveStatement runContext {catalog := database.catalog}
    (.pragma (.tableInfo (name! "v"))) with | .ok _ => true | .error _ => false) = true := by decide +kernel

/-- The table-only metadata primitive refuses a view instead of reporting no columns. -/
example : database.catalog.tableInfoRows (name! "v") = none := by decide +kernel

/-- The SQL metadata function is also unmodeled until it can expand the view definition. -/
example : ¬ Holds (sql r"SELECT 1 FROM pragma_table_info('v')") database ∧
    ¬ Empty (sql r"SELECT 1 FROM pragma_table_info('v')") database ∧
    ¬ Fails (sql r"SELECT 1 FROM pragma_table_info('v')") database := by decide +kernel

/-- Foreign-key listing reads only the declared object's table keys, so a view gives no rows. -/
example : Empty (sql r"PRAGMA foreign_key_list(v)") database := by decide +kernel

/-- A view has no child rows to check, even when its SELECT cannot currently resolve. -/
example : Empty (sql r"PRAGMA foreign_key_check(v)") database := by decide +kernel

/-- Integrity checks inspect stored tables; naming a view succeeds without expanding it. -/
example : Holds (sql r"PRAGMA integrity_check(v)") database ∧
    Holds (sql r"PRAGMA quick_check(v)") database := by decide +kernel

/-- A view whose name shadows the pragma function must not expose the function's rows. -/
def shadows : Database := ⟨(Catalog.createView [] (name! "pragma_table_info") late).emptyDatabase, by decide +kernel⟩

/-- A view shadows the pragma function and reports SQLite's not-a-function error. -/
example : Fails (sql r"SELECT 1 FROM pragma_table_info('v')") shadows := by decide +kernel

end ViewCatalogExamples
