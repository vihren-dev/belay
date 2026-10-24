import Belay.Sqlite.ReplayValues
import Belay.Sqlite.Database

set_option doc.verso true

/-! SQL reconstruction for generated, ordinary table schemas. More complex explicit
witnesses can retain their original db! construction. Every spelling here remains a proposal
until replay validation reconstructs the exact catalog, rowids and values. -/

namespace Belay.Sqlite.Replay

open Belay.Sqlite.Model

/-- Render the ordinary column properties used by inferred and explicit simple schemas.
Defaults, CHECK constraints, foreign keys and generated columns need the original construction
text. Returning none keeps unsupported reconstruction explicit. -/
private def columnSql (column : CatalogColumn) : Option String := do
  guard (column.defaultValue.isNone && column.checks.isEmpty && column.foreignKeys.isEmpty &&
    column.generated.isNone && column.notNullAlgorithm == .abort)
  let name ← identifier column.name
  let declared ← match column.declaredType with
    | none => pure ""
    | some text => (" " ++ ·) <$> identifier (Identifier.ofString text)
  return name ++ declared ++ " COLLATE " ++ column.collation.sqlName ++
    (if column.notNull then " NOT NULL" else "")

/-- Render a table without keys or table constraints. The complete construction is validated
later; an unsupported schema uses an explicit construction or produces unknown replay. -/
private def tableSql (name : Identifier) (table : CatalogTable) : Option String := do
  guard (table.primaryKey.isEmpty && table.rowidAlias.isNone && table.uniqueKeys.isEmpty &&
    table.checks.isEmpty && table.foreignKeys.isEmpty && !table.withoutRowid)
  let quoted ← identifier name
  let columns ← table.columns.mapM columnSql
  return "CREATE TABLE " ++ quoted ++ " (" ++ String.intercalate ", " columns ++ ")" ++
    (if table.strict then " STRICT" else "") ++ ";\n"

/-- Insert one row using SQLite's generated rowid. The model does not support explicit
implicit-rowid INSERT columns, so exact reconstruction rejects nonsequential rowids.
Every cell uses the shared storage-preserving spelling, including NULL, BLOB and text. -/
private def rowSql (name : Identifier) (table : CatalogTable) (row : Row) : Option String := do
  let columns ← (table.columns.map (·.name)).mapM identifier
  let values ← row.values.mapM valueLiteral
  let quoted ← identifier name
  return "INSERT INTO " ++ quoted ++ " (" ++ String.intercalate ", " columns ++ ") VALUES (" ++
    String.intercalate ", " values ++ ");\n"

/-- Propose ordinary-table SQL while calling the supplied resource action before and after
each table or row fragment. Inputs are database data, not expressions to evaluate. The action
can bound accumulated text or check cancellation. Every result still needs exact reconstruction
validation; use {lit}`databaseSql` below for ordinary pure formatting. -/
def databaseSqlWith [Monad m] (check : String → m Unit) (database : Database) : m (Option String) := do
  let mut fragments := []
  for (object, position) in database.raw.catalog.zipIdx do
    check ""
    match object.entry with
    | .table table =>
      let some create := tableSql object.name table | return none
      check create
      fragments := create :: fragments
      for row in database.raw.rows.getD position [] do
        check ""
        let some insert := rowSql object.name table row | return none
        check insert
        fragments := insert :: fragments
    | .index _ | .trigger _ => return none
  return some (String.join fragments.reverse)

/-- Propose SQL that builds a database with ordinary tables and no indexes or triggers.
The empty database gives empty text. Unsupported catalog forms or unrepresentable values
return none. This function alone does not certify that reconstruction matches the witness. -/
def databaseSql (database : Database) : Option String :=
  Id.run (databaseSqlWith (fun _ => pure ()) database)

end Belay.Sqlite.Replay
