import Belay

/-! Manually supplied view definitions exercise the catalog boundary before SQL view
expansion is enabled. Reads and writes that need expansion must remain unmodeled;
they must not produce a fabricated missing-table error or an empty metadata result. -/

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

/-- Every statement listed here requires view expansion at this interim catalog boundary. -/
def deferred : List Syntax.Statement := [
  .select [.star] (some {table := name! "v", alias := none}) [] none [] [] none none,
  .insert (name! "v") none [[.numeric "1"]] [],
  .insert (name! "v") none [[.numeric "1"]] [] (subqueries := [late.query]),
  .update (name! "v") [(name! "x", .numeric "1")] none,
  .delete (name! "v") none,
  .createIndex (name! "i") false (name! "v") [⟨.identifier (name! "x") .none, false⟩] none,
  .addColumn (name! "v") {name := name! "y", declaredType := none, constraints := []},
  .dropTable (name! "v") false,
  .dropTable (name! "v") true,
  .createTrigger (name! "tr") false .before .insert (name! "v") none [],
  .pragma (.tableInfo (name! "v")) ]

/-- None of these paths fabricates a native prepare error for the unresolved view. -/
example : deferred.all (fun statement => match resolveStatement runContext
    {catalog := database.catalog} statement with | .error _ => true | .ok _ => false) = true := by decide +kernel

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

/-- View shadowing remains a model restriction, rather than a successful or empty query. -/
example : ¬ Holds (sql r"SELECT 1 FROM pragma_table_info('v')") shadows ∧
    ¬ Empty (sql r"SELECT 1 FROM pragma_table_info('v')") shadows ∧
    ¬ Fails (sql r"SELECT 1 FROM pragma_table_info('v')") shadows := by decide +kernel

end ViewCatalogExamples
