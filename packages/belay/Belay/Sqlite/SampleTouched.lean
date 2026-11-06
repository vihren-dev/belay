import Belay.Sqlite.SampleScriptHints
import Belay.Sqlite.Database

set_option doc.verso true

/-! The touched tables of a claim: the tables that its statements read or write, and the tables
that SQLite reads or writes for them through triggers, views and foreign keys. The search fills
only these tables, so that a large schema does not multiply its candidates. The result is a
choice of candidates only: certification decides every result. -/

namespace Belay.Sqlite.Sampling

open Belay.Sqlite.Model

/-- The tables and views that a statement reads or writes, by name: the named sources of its
queries and subqueries and its write target ({name}`statementHints`). Transaction control names
none. None for every other statement, for example ALTER TABLE, CREATE TRIGGER or a PRAGMA,
whose tables the hints do not name: then every table counts as touched. -/
def statementTables (statement : Syntax.Statement) : Option (List Identifier) :=
  match statement with
  | .select .. | .insert .. | .insertSelect .. | .update .. | .delete .. =>
    some ((statementHints statement).sources.map (·.table))
  | .begin | .commit | .rollback => some []
  | _ => none

/-- The names of the tables and views that a list of statements reads or writes
({name}`statementTables`), or none when one of them does not name its tables. -/
def statementsTables (statements : List Syntax.Statement) : Option (List Identifier) :=
  statements.foldlM (fun names statement => (names ++ ·) <$> statementTables statement) []

/-- The foreign keys of a table: those of its columns, then those of the table. -/
def allForeignKeys (table : CatalogTable) : List ForeignKey :=
  table.columns.flatMap (·.foreignKeys) ++ table.foreignKeys

/-- The names that one catalog object adds to a set of touched names, or none when it makes
every table touched:
- a touched table adds the parents of its foreign keys;
- a table with a foreign key to a touched table is added, because the actions and checks of
  the key run when the parent changes;
- a trigger on a touched table adds the tables of its body ({name}`statementsTables`);
- a touched view adds the tables of its query and subqueries. -/
def objectTables (touched : List Identifier) (object : CatalogObject) : Option (List Identifier) :=
  let isTouched (name : Identifier) := touched.any (·.sameName name)
  match object.entry with
  | .table table =>
    let parents := (allForeignKeys table).map (·.table)
    if isTouched object.name then some parents
    else if parents.any isTouched then some [object.name]
    else some []
  | .trigger trigger =>
    if isTouched trigger.table then statementsTables (trigger.body.map (·.statement)) else some []
  | .view view =>
    if isTouched object.name then
      some ((view.query :: view.subqueries).flatMap fun query => (subqueryHints query).sources.map (·.table))
    else some []
  | .index _ => some []

/-- The touched names of a catalog: the given names, closed under {name}`objectTables`, or none
when every table counts as touched. Each round adds a name of the catalog or stops, so the
fuel of one round per object and one more suffices. -/
def touchedNames (catalog : Catalog) (names : List Identifier) : Option (List Identifier) :=
  go (catalog.length + 1) names
where
  /-- One round of the closure, with the remaining fuel. -/
  go : Nat → List Identifier → Option (List Identifier)
    | 0, _ => none
    | fuel + 1, names => do
      let added ← catalog.foldlM (fun found object => (found ++ ·) <$> objectTables names object) []
      let named := added.filter fun name =>
        !names.any (·.sameName name) && catalog.any (·.name.sameName name)
      if named.isEmpty then return names
      go fuel (names ++ named.eraseDups)

/-- Whether the search fills a catalog object: a table among the touched names. With none,
every table. -/
def fills (touched : Option (List Identifier)) (object : CatalogObject) : Bool :=
  match object.entry with
  | .table _ => touched.all fun names => names.any (·.sameName object.name)
  | .index _ | .trigger _ | .view _ => false

/-- The database without the rows of the tables that the search does not fill ({name}`fills`). -/
def onlyTouched (touched : Option (List Identifier)) (raw : Database.Raw) : Database.Raw :=
  { raw with rows := raw.catalog.zipIdx.map fun (object, position) =>
      if fills touched object then raw.rows.getD position [] else [] }

end Belay.Sqlite.Sampling
