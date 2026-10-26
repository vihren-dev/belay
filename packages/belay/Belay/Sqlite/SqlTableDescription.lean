import Belay.Sqlite.Run
import Lean.Data.Name

set_option doc.verso true

/-! The hover text of a table: the catalog facts of {name}`Belay.Sqlite.Model.CatalogTable` in plain words, and the
row count when the editor knows the rows. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- The SQL name of a collation, for example {assert}`collationName .nocase = "NOCASE"`. -/
def collationName : Collation → String
  | .binary => "BINARY"
  | .nocase => "NOCASE"
  | .rtrim => "RTRIM"

/-- The words after a column name in the hover: the declared type, or {lit}`no declared type`, then
{lit}`PRIMARY KEY` when the column is in the primary key, {lit}`NOT NULL`, {lit}`UNIQUE` when a
single-column unique constraint holds it, and {lit}`COLLATE` with a collation other than
{lit}`BINARY`. -/
def columnFacts (table : CatalogTable) (position : Nat) (column : CatalogColumn) : String :=
  let unique := table.uniqueKeys.any (· == [position])
  let facts : List String :=
    [column.declaredType.getD "no declared type"] ++
    (if table.primaryKey.contains position then ["PRIMARY KEY"] else []) ++
    (if column.notNull then ["NOT NULL"] else []) ++
    (if unique then ["UNIQUE"] else []) ++
    (if column.collation == .binary then [] else [s!"COLLATE {collationName column.collation}"])
  ", ".intercalate facts

/-- The line about the rows: the count, or nothing when the editor does not know the rows. -/
def rowsLine : Option Nat → List String
  | some 1 => ["1 row at this point of the script."]
  | some count => [s!"{count} rows at this point of the script."]
  | none => []

/-- The Markdown hover of the table {lit}`name` in the database called {lit}`owner` (a Lean
declaration, when the database term is one): the columns with their declared types and
constraints, the table options, and the row count when {lit}`rows` holds it. For example, the table
{lit}`t(a INTEGER PRIMARY KEY)` of {lit}`shop` with two rows reads
{lit}`Table t of shop. 1 column. ... 2 rows at this point of the script.` -/
def tableDescription (owner : Option Lean.Name) (name : Identifier) (table : CatalogTable)
    (rows : Option Nat) : String :=
  let where_ := owner.elim "" fun database => s!" of `{database}`"
  let columns := table.columns.zipIdx.map fun (column, position) =>
    s!"- `{column.name}`: {columnFacts table position column}"
  let options := (if table.withoutRowid then ["WITHOUT ROWID"] else []) ++ (if table.strict then ["STRICT"] else [])
  "\n".intercalate ([s!"Table `{name}`{where_}."] ++ columns ++
    (if options.isEmpty then [] else [", ".intercalate options ++ "."]) ++ rowsLine rows)

end Belay.Sqlite
