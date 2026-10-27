import Belay.Sqlite.Model.Resolution.RenameCatalog
import Belay.Sqlite.Model.Resolution.CatalogOutline
import Belay.Sqlite.Model.Resolution.RewriteExamples

set_option doc.verso true

/-! Examples of the catalog after a rename ({lit}`renameCatalog`), checked by {lit}`#guard` when the package
builds. One catalog holds every kind of object that a rename reads: a table with a CHECK and a primary key, a
table with a foreign key to it, an index, a view, a table, and a trigger on the first table. The examples check
the objects after a table rename and a column rename, the errors of SQLite for a definition that does not resolve
before or after the rename, and that the new catalog keeps the outline and the selected parents
({lit}`Catalog.keepsOutline`), which the run of the rewrite tests. -/

namespace Belay.Sqlite.Model.Resolution.RenameCatalogExamples

open Belay.Sqlite.Model Syntax Resolution.Examples Resolution.RewriteExamples

/-- The text {lit}`a > 0` with the token of the column. -/
def positive : SourceText := { text := "a > 0", tokens := [{ paths := [[1]], start := 0, stop := 1, quote := .none }] }

/-- The catalog {lit}`t(a PRIMARY KEY CHECK (a > 0), b)`, {lit}`c(ta REFERENCES t(a), x)`, the index {lit}`ti`
on {lit}`t(a)`, the view {lit}`v` of {lit}`SELECT a FROM t`, {lit}`u(x)`, and the trigger {lit}`g`
({lit}`AFTER UPDATE OF a ON t BEGIN INSERT INTO u(x) VALUES (new.a); END`), at the positions 0 to 5. -/
def base : Catalog := catalogOf (schema [
  .createTable (name! "t") [
    { name := name! "a", declaredType := some "TEXT",
      constraints := [.primaryKey false, .check (.compare .gt (ident "a") (.numeric "0")) "a > 0" positive] },
    column (name! "b")] [],
  .createTable (name! "c") [
    { name := name! "ta", declaredType := some "TEXT",
      constraints := [.references (name! "t") [name! "a"] .noAction .noAction] },
    column (name! "x")] [],
  .createIndex (name! "ti") false (name! "t") [key (name! "a")] none,
  .createView (name! "v") false none (selectOf [ident "a"]),
  .createTable (name! "u") [column (name! "x")] [],
  .createTrigger (name! "g") false .after (.update [name! "a"]) (name! "t") none
    [.insert (name! "u") (some [name! "x"]) [[dotted "new" "a"]] []]])

/-- The rename of the table {lit}`t` to {lit}`w`. -/
def tableToW : RenameRequest := { target := .table 0, new := name! "w", style := .table }

/-- The rename of the column {lit}`t.a` to {lit}`z`, written without a quote. -/
def columnToZ : RenameRequest := { target := .column 0 0, new := name! "z", style := .column false }

/-- The catalog after the rename, or none when the rename fails. -/
def renamedBy (catalog : Catalog) (request : RenameRequest) (oldTable oldColumn : String) : Option Catalog :=
  (renameCatalog context catalog request (Identifier.ofString oldTable) (Identifier.ofString oldColumn)).toOption

/-- The prepare error of SQLite when the rename fails with one. -/
def errorBy (catalog : Catalog) (request : RenameRequest) (oldTable oldColumn : String) : Option PrepareError :=
  match renameCatalog context catalog request (Identifier.ofString oldTable) (Identifier.ofString oldColumn) with
  | .error (.prepare error) => some error
  | .error (.restricted _) | .ok _ => none

/-- The table at the position of a catalog. -/
def tableIn (catalog : Option Catalog) (position : Nat) : Option CatalogTable :=
  catalog.bind (·.tableAt position)

-- A table rename: the names of the objects, the foreign key of the other table, the view and the trigger.
#guard ((renamedBy base tableToW "t" "t").map (·.map (·.name))) ==
  some [name! "w", name! "c", name! "ti", name! "v", name! "u", name! "g"]
#guard ((tableIn (renamedBy base tableToW "t" "t") 1).map fun table => table.allForeignKeys.map (·.table)) ==
  some [name! "w"]
#guard ((renamedBy base tableToW "t" "t").bind fun catalog => catalog[3]?.map (·.entry)) ==
  some (.view { query := selectOf [ident "a"] |> fun query => { query with source := some { table := name! "w", alias := none } } })
#guard ((renamedBy base tableToW "t" "t").bind fun catalog => catalog[5]?.map (·.entry)) ==
  (base[5]?.map fun object => match object.entry with
    | .trigger trigger => .trigger { trigger with table := name! "w" }
    | .table _ | .index _ | .view _ => object.entry)
-- The CHECK label of the renamed table does not name the table, so it stays.
#guard ((tableIn (renamedBy base tableToW "t" "t") 0).map fun table => table.columns.flatMap (·.checks.map (·.label))) ==
  some ["a > 0"]
-- The new catalog keeps the outline and the parents that the foreign keys select.
#guard (renamedBy base tableToW "t" "t").any base.keepsOutline

-- A column rename: the column, the label of its CHECK, the referenced column, the view and the trigger.
#guard ((tableIn (renamedBy base columnToZ "t" "a") 0).map fun table => table.columns.map (·.name)) ==
  some [name! "z", name! "b"]
#guard ((tableIn (renamedBy base columnToZ "t" "a") 0).map fun table => table.columns.flatMap (·.checks.map (·.label))) ==
  some ["z > 0"]
#guard ((tableIn (renamedBy base columnToZ "t" "a") 1).map fun table => table.allForeignKeys.map (·.referenced)) ==
  some [[name! "z"]]
#guard ((renamedBy base columnToZ "t" "a").bind fun catalog => catalog[3]?.map (·.entry)) ==
  some (.view { query := selectOf [ident "z"] })
#guard ((renamedBy base columnToZ "t" "a").bind fun catalog => catalog[5]?.map (·.entry)) ==
  (base[5]?.map fun object => match object.entry with
    | .trigger trigger => .trigger { trigger with
        event := .update [name! "z"]
        body := [.insert (name! "u") (some [name! "x"]) [[dotted "new" "z"]] []] }
    | .table _ | .index _ | .view _ => object.entry)
#guard (renamedBy base columnToZ "t" "a").any base.keepsOutline

-- A rename of a column of an unrelated table leaves the view and the trigger as they are.
#guard ((renamedBy base { columnToZ with target := .column 1 1 } "c" "x").bind fun catalog => catalog[3]?.map (·.entry)) ==
  (base[3]?.map (·.entry))
#guard ((renamedBy base { columnToZ with target := .column 1 1 } "c" "x").bind fun catalog => catalog[5]?.map (·.entry)) ==
  (base[5]?.map (·.entry))
-- The column list of the INSERT in the trigger names the column of {lit}`u`, so a rename of {lit}`u.x` changes it.
#guard ((renamedBy base { columnToZ with target := .column 4 0 } "u" "x").bind fun catalog => catalog[5]?.map (·.entry)) ==
  (base[5]?.map fun object => match object.entry with
    | .trigger trigger => .trigger { trigger with
        body := [.insert (name! "u") (some [name! "z"]) [[dotted "new" "a"]] []] }
    | .table _ | .index _ | .view _ => object.entry)

/-- {lit}`SELECT "z", a FROM t`: the double-quoted {lit}`"z"` is a string literal while no column has that name. -/
def quotedView : Subquery :=
  { selectOf [ident "a"] with columns := [.expression (.identifier (name! "z") .double) none "", .expression (ident "a") none ""] }

/-- The catalog with the table {lit}`t(a, b)` and the view {lit}`q` of {lit}`quotedView`. -/
def quoted : Catalog := catalogOf (schema [.createTable (name! "t") [column (name! "a"), column (name! "b")] [],
  .createView (name! "q") false none quotedView])

-- SQLite writes a double-quoted string literal of a view with single quotes at every column rename, so that a column
-- that gets the name of the literal does not take its place ({lit}`renameQuotefix`). A table rename leaves it as written.
#guard ((renamedBy quoted columnToZ "t" "a").bind fun catalog => catalog[1]?.map (·.entry)) ==
  some (.view { query := { quotedView with columns := [.expression (.string [122]) none "", .expression (ident "z") none ""] } })
#guard ((renamedBy quoted tableToW "t" "t").bind fun catalog => catalog[1]?.map (·.entry)) ==
  some (.view { query := { quotedView with
    source := some { table := name! "w", alias := none }
    columns := [.expression (.identifier (name! "z") .double) none "", .expression (ident "a") none ""] } })

/-- The text {lit}`"z"` of a result column, and the same text after the quote is fixed: a result column
without an alias has its text as its name. -/
def doubleQuotedText : SourceText :=
  { text := "\"z\"", tokens := [{ paths := [[]], start := 0, stop := 3, quote := .double }] }

/-- The text {lit}`'z'` that SQLite writes for {lit}`doubleQuotedText`. -/
def singleQuotedText : SourceText :=
  { text := "'z'", tokens := [{ paths := [[]], start := 0, stop := 3, quote := .single }] }

/-- The view {lit}`SELECT "z" FROM t`, whose column is named by its text. -/
def namedByText : Catalog := catalogOf (schema [.createTable (name! "t") [column (name! "a"), column (name! "b")] [],
  .createView (name! "q") false none
    { selectOf [ident "a"] with columns := [.expression (.identifier (name! "z") .double) none doubleQuotedText] }])

-- The name of the view column is the text of its expression, so the fixed quote shows in the name.
#guard ((renamedBy namedByText columnToZ "t" "a").bind fun catalog => catalog[1]?.map (·.entry)) ==
  some (.view { query := { selectOf [ident "z"] with columns := [.expression (.string [122]) none singleQuotedText] } })

end Belay.Sqlite.Model.Resolution.RenameCatalogExamples
