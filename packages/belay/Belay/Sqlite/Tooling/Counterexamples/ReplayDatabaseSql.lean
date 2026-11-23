import Belay.Sqlite.Tooling.Counterexamples.ReplayTableSql
import Belay.Sqlite.Schema.Rows.Database

set_option doc.verso true

/-! SQL reconstruction for computed catalogs. The replay checker runs the proposed construction
and compares its catalog, rowids and values with the witness. -/

namespace Belay.Sqlite.Replay

open Belay.Sqlite.Model

/-- Insert one row using SQLite's generated rowid. The model does not support explicit
implicit-rowid INSERT columns, so exact reconstruction rejects nonsequential rowids.
Every cell uses the shared storage-preserving spelling, including NULL, BLOB and text.
An INTEGER PRIMARY KEY column gets its value, which is the rowid. -/
def rowSql (name : Identifier) (table : CatalogTable) (row : Row) : Option String := do
  guard (row.values.length == table.columns.length)
  let writable := (table.columns.zip row.values).filter fun pair => pair.1.generated.isNone
  let columns ← writable.mapM fun pair => identifier pair.1.name
  let values ← writable.mapM fun pair => valueLiteral pair.2
  let quoted ← identifier name
  return "INSERT INTO " ++ quoted ++ " (" ++ String.intercalate ", " columns ++ ") VALUES (" ++
    String.intercalate ", " values ++ ");\n"

/-- Propose a SQL construction from the catalog. Visit catalog entries in order and insert
each table's rows immediately after its creation. Generated columns are computed by INSERT.
Call the resource check before and after each statement. Exact reconstruction is checked
by the replay consumer before the SQL is used. -/
def databaseSqlWith [Monad m] (check : String → m Unit) (database : Database) : m (Option String) := do
  let mut fragments := []
  for (object, position) in database.raw.catalog.zipIdx do
    check ""
    let create := match object.entry with
      | .table table => tableSql object.name table
      | .index idx => indexSql database.raw.catalog object.name idx
      | .view view => viewSql object.name view
      | .trigger trigger => triggerSql object.name trigger
    let some sql := create | return none
    check sql
    fragments := sql :: fragments
    if let .table table := object.entry then
      for row in database.raw.rows.getD position [] do
        check ""
        let some insert := rowSql object.name table row | return none
        check insert
        fragments := insert :: fragments
  return some (String.join fragments.reverse)

/-- Propose SQL for a computed database. The empty database gives empty text. A stored value
that has no SQL spelling gives none. Exact replay checks the proposed construction. -/
def databaseSql (database : Database) : Option String :=
  Id.run (databaseSqlWith (fun _ => pure ()) database)

end Belay.Sqlite.Replay
