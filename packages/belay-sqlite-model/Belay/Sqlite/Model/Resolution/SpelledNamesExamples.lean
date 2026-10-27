import Belay.Sqlite.Model.Resolution.RenameCatalogExamples
import Belay.Sqlite.Model.Resolution.SpelledNames

set_option doc.verso true

/-! Examples of the facts about the text of a definition ({lit}`CatalogTable.inlineUnique`,
{lit}`CatalogTable.exactNames`, {lit}`CatalogIndex.exactNames`, {lit}`CatalogTable.quotedRename`), checked by
{lit}`#guard` in the compiled evaluator when the package builds. The facts decide how the error of SQLite is
spelled when a later DROP COLUMN leaves a definition without its column. -/

namespace Belay.Sqlite.Model.Resolution.SpelledNamesExamples

open Belay.Sqlite.Model Syntax Resolution.Examples Resolution.RenameCatalogExamples

/-- The facts of the first table of a catalog: the columns with UNIQUE, and whether the names are exact. -/
def factsOf (catalog : Catalog) : Option (List Nat × Bool) :=
  (catalog.tableAt 0).map fun table => (table.inlineUnique, table.exactNames)

/-- A column {lit}`a` with the constraint, and the column {lit}`b`. -/
def withConstraint (constraint : ColumnConstraint) : List ColumnDefinition :=
  [{ name := name! "a", declaredType := some "TEXT", constraints := [constraint] }, column (name! "b")]

-- A UNIQUE column constraint is noted by position; a table-level UNIQUE is not.
#guard factsOf (catalogOf (schema [.createTable (name! "t") (withConstraint (.unique none)) []])) == some ([0], true)
#guard factsOf (catalogOf (schema [.createTable (name! "t") (withConstraint (.notNull none)) [.unique [name! "b"] none]])) ==
  some ([], true)

-- A table-level UNIQUE or FOREIGN KEY that names a column in another case is not exact.
#guard factsOf (catalogOf (schema [.createTable (name! "t") (withConstraint (.notNull none)) [.unique [name! "B"] none]])) ==
  some ([], false)

-- The index notes the same: a key that spells the column as declared is exact, another case is not.
#guard match (catalogOf (schema [.createTable (name! "t") (withConstraint (.notNull none)) [],
    .createIndex (name! "i") false (name! "t") [key (name! "b")] none]))[1]?.map (·.entry) with
  | some (CatalogEntry.index index) => index.exactNames
  | _ => false
#guard match (catalogOf (schema [.createTable (name! "t") (withConstraint (.notNull none)) [],
    .createIndex (name! "i") false (name! "t") [key (name! "B")] none]))[1]?.map (·.entry) with
  | some (CatalogEntry.index index) => !index.exactNames
  | _ => false

-- A quoted new name of a column rename is noted on the table, an unquoted one is not.
#guard (tableIn (renamedBy base { columnToZ with style := .column true } "t" "a") 0).map (·.quotedRename) == some true
#guard (tableIn (renamedBy base columnToZ "t" "a") 0).map (·.quotedRename) == some false

end Belay.Sqlite.Model.Resolution.SpelledNamesExamples
