import Belay.Sqlite.Model.Resolution.RenameCatalogExamples
import Belay.Sqlite.Model.Resolution.GeneratedExamples
import Belay.Sqlite.Model.Resolution.DropColumnResolve

set_option doc.verso true

/-! Examples of ALTER TABLE DROP COLUMN, checked by {lit}`#guard` when the package builds, with the messages of
SQLite 3.51.0 that the task probed natively: the order of the early checks, the schema tests before and after the
edit ({lit}`error in index i after drop column: ...`), the definitions that still name the column, and the drops that
the model restricts. A drop that passes every check is the statement {lit}`Resolved.Statement.dropColumn` with the
catalog after the drop, and the run of that statement keeps the rows that the other columns hold. -/

namespace Belay.Sqlite.Model.Resolution.DropColumnExamples

open Belay.Sqlite.Model Syntax Resolution.Examples Resolution.RewriteExamples Resolution.GeneratedExamples

/-- The text {lit}`b > 0` with the token of the column {lit}`b`, the second column. -/
def positiveB : SourceText := { text := "b > 0", tokens := [{ paths := [[1]], start := 0, stop := 1, quote := .none }] }

/-- The schema of the examples: the table {lit}`t(a, b, c)`, the index {lit}`ti` on {lit}`t(a)`, the view {lit}`v` of
{lit}`SELECT a FROM t`, the table {lit}`u(x)`, the table {lit}`k(p, q)` with a primary key on {lit}`p`, the table
{lit}`h(a, b, CHECK (b > 0))`, and the table {lit}`g(a, b, c AS (b + 1))`. -/
def objects : Catalog := catalogOf (schema [
  .createTable (name! "t") [column (name! "a"), column (name! "b"), column (name! "c")] [],
  .createIndex (name! "ti") false (name! "t") [key (name! "a")] none,
  .createView (name! "v") false none (selectOf [ident "a"]),
  .createTable (name! "u") [column (name! "x")] [],
  .createTable (name! "k") [column (name! "p"), column (name! "q")] [.primaryKey [name! "p"]],
  .createTable (name! "h") [column (name! "a"), column (name! "b")]
    [.check (.compare .gt (ident "b") (.numeric "0")) "b > 0" positiveB],
  .createTable (name! "g") [column (name! "a") (some "INTEGER"), column (name! "b") (some "INTEGER"),
    gen (name! "c") (.arithmetic .add (ref (name! "b")) (.numeric "1"))] []])

/-- The text {lit}`A > 0` with the token of the column {lit}`a`, spelled with a capital. -/
def positiveUpperA : SourceText := { text := "A > 0", tokens := [{ paths := [[1]], start := 0, stop := 1, quote := .none }] }

/-- The catalog with the table {lit}`gg(a, b AS (5))`, whose only other column is generated. -/
def onlyGenerated : Catalog := catalogOf (schema [
  .createTable (name! "gg") [column (name! "a"), gen (name! "b") (.numeric "5")] []])

/-- The catalog with the table {lit}`w(a CHECK (a > 0), b, CHECK (A > 0))`: the CHECK constraint of the column goes with
it, and the one of the table stays and names the column. -/
def withTwoChecks : Catalog := catalogOf (schema [
  .createTable (name! "w")
    [{ column (name! "a") with constraints := [.check (.compare .gt (ident "a") (.numeric "0")) "a > 0"] }, column (name! "b")]
    [.check (.compare .gt (ident "A") (.numeric "0")) "A > 0" positiveUpperA]])

/-- The catalog with a table {lit}`f` that has a foreign key from {lit}`b` to {lit}`t(a)`. -/
def withChild : Catalog := catalogOf (schema [
  .createTable (name! "t") [column (name! "a"), column (name! "b")] [.primaryKey [name! "a"]],
  .createTable (name! "f") [column (name! "a"), column (name! "b")]
    [.foreignKey [name! "b"] (name! "t") [name! "a"] .noAction .noAction]])

/-- The catalog with an index {lit}`ti` on {lit}`t(c)`, the third column: a drop of the second column moves the
position that the index reads. -/
def shifted : Catalog := catalogOf (schema [
  .createTable (name! "t") [column (name! "a"), column (name! "b"), column (name! "c")] [],
  .createIndex (name! "ti") false (name! "t") [key (name! "c")] none])

/-- The prepare error of one statement from a catalog, or none. -/
def errorIn (catalog : Catalog) (statement : Syntax.Statement) : Option PrepareError :=
  match statements (migration catalog [statement]) with
  | [.prepareError error] => some error
  | _ => none

/-- Whether the statement resolves to a drop of a column, and the drop runs on the empty database of the catalog:
the run succeeds with the catalog that the resolution gives. -/
def dropsAndRuns (catalog : Catalog) (statement : Syntax.Statement) : Bool :=
  let result := migration catalog [statement]
  match statements result with
  | [resolved@(.dropColumn _ _ stored)] =>
    match step 0 {} [] resolved catalog.emptyDatabase with
    | .ok database => stored == catalogOf result && database.catalog == stored
    | .error _ => false
  | _ => false

/-- The drop of a column, as the statement writes it. -/
def drop (table column : String) : Syntax.Statement :=
  .dropColumn (Identifier.ofString table) (Identifier.ofString column) column

-- The checks on the table and the column, in the order of SQLite.
#guard errorIn objects (drop "nope" "a") == some (.noSuchTable (name! "nope"))
#guard errorIn objects (drop "ti" "a") == some (.noSuchTable (name! "ti"))
#guard errorIn objects (drop "sqlite_schema" "sql") == some (.expression (.tableMayNotBeAltered (name! "sqlite_master")))
#guard errorIn objects (drop "V" "a") == some (.dropColumn (.view (name! "v")))
#guard errorIn objects (.dropColumn (name! "t") (name! "zz") "\"zz\"") == some (.renameNoSuchColumn "\"zz\"")
-- A primary key column, and the last column; the message prints the column as the statement writes it.
#guard errorIn objects (drop "k" "p") == some (.dropColumn (.primaryKey (name! "p")))
#guard errorIn objects (drop "k" "P") == some (.dropColumn (.primaryKey (name! "P")))
#guard errorIn objects (drop "u" "x") == some (.dropColumn (.lastColumn (name! "x")))

-- A drop that passes every check is the statement with the catalog after the drop, and it runs.
-- An index on a column after the dropped one stays valid; the index on the dropped column is the one that fails.
#guard dropsAndRuns shifted (drop "t" "b")
#guard errorIn shifted (drop "t" "c") ==
  some (.dependentObject .index (name! "ti") .afterDropColumn (.expression (.noSuchColumn (name! "c"))))
#guard dropsAndRuns objects (drop "t" "c")
#guard dropsAndRuns objects (drop "t" "B")
#guard dropsAndRuns objects (drop "k" "q")
#guard dropsAndRuns objects (drop "g" "c")
#guard dropsAndRuns objects (drop "h" "a")

/-- The database of {lit}`objects` with two rows in {lit}`t` (rowids 1 and 5, one NULL cell) and one row in {lit}`u`. -/
def populated : Database :=
  let empty := objects.emptyDatabase
  { empty with rows := ((empty.rows.modify 0 fun _ =>
      [{ rowid := 1, values := [.integer 1, .integer 2, .integer 3] },
       { rowid := 5, values := [.integer 4, .null, .integer 6] }]).modify 3 fun _ =>
      [{ rowid := 7, values := [.integer 9] }]) }

/-- The rows of the database after the resolved statement ran, or none when the run failed. -/
def rowsAfter (database : Database) (statement : Syntax.Statement) : Option (List (List Row)) :=
  match statements (migration database.catalog [statement]) with
  | [resolved] => match step 0 {} [] resolved database with
    | .ok after => some after.rows
    | .error _ => none
  | _ => none

-- A drop with rows removes the cell and keeps the other cells in their order, the rowids and the other tables.
#guard rowsAfter populated (drop "t" "b") ==
  some ((populated.rows.modify 0 fun _ =>
    [{ rowid := 1, values := [.integer 1, .integer 3] }, { rowid := 5, values := [.integer 4, .integer 6] }]))
#guard rowsAfter populated (drop "t" "c") ==
  some ((populated.rows.modify 0 fun _ =>
    [{ rowid := 1, values := [.integer 1, .integer 2] }, { rowid := 5, values := [.integer 4, .null] }]))
-- A statement that the resolver refuses leaves no run, so the database stays; the run itself also refuses a catalog
-- of the statement that is not the catalog after the drop, and then fails with the database unchanged.
#guard rowsAfter populated (drop "t" "a") == none
#guard match step 0 {} [] (.dropColumn 0 1 objects) populated with
  | .error (_, after) => after == populated
  | .ok _ => false

-- The schema test after the edit finds, in schema order, the first object that no longer resolves: here the
-- index comes before the view.
#guard errorIn objects (drop "t" "a") ==
  some (.dependentObject .index (name! "ti") .afterDropColumn (.expression (.noSuchColumn (name! "a"))))
-- A table that still names the column: a CHECK constraint (the name as written), a generated column.
#guard errorIn objects (drop "h" "b") ==
  some (.dependentObject .table (name! "h") .afterDropColumn (.expression (.noSuchColumn (name! "b"))))
#guard errorIn objects (drop "g" "b") ==
  some (.dependentObject .table (name! "g") .afterDropColumn (.expression (.noSuchColumn (name! "b"))))

-- A table whose remaining columns are all generated; and a CHECK constraint of the table that reads the column
-- under another letter case while the column keeps a CHECK of its own, which goes with the column: the error names
-- the spelling of the constraint that stays.
#guard errorIn onlyGenerated (drop "gg" "a") ==
  some (.dependentObject .table (name! "gg") .afterDropColumn (.expression .onlyGeneratedColumns))
#guard errorIn withTwoChecks (.dropColumn (name! "w") (name! "a") "a") ==
  some (.dependentObject .table (name! "w") .afterDropColumn (.expression (.noSuchColumn (name! "A"))))

-- A table that is the parent of a foreign key is outside the model, and so is a foreign key that names the column
-- as a child column when the error is not known. The error of the child column is known.
#guard restricted (migration withChild [drop "t" "b"])
#guard errorIn withChild (drop "f" "b") ==
  some (.dependentObject .table (name! "f") .afterDropColumn (.expression (.unknownForeignKeyColumn (name! "b"))))
#guard dropsAndRuns withChild (drop "f" "a")

end Belay.Sqlite.Model.Resolution.DropColumnExamples
