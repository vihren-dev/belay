import Belay.Sqlite.Model.Resolution.Context
import Belay.Sqlite.Model.Resolution.CatalogDrop

set_option doc.verso true

/-! Name resolution of DROP TABLE and DROP INDEX (ADR 0014, D7), in the order of SQLite
3.51.0's {lit}`sqlite3DropTable` and {lit}`sqlite3DropIndex`, with names compared with ASCII
case ignored. Checked natively with 3.51.0. -/

namespace Belay.Sqlite.Model

/-- The name that SQLite reports for one of its schema tables, or none for another name:
{lit}`sqlite_master` for {lit}`sqlite_master` and {lit}`sqlite_schema`, and
{lit}`sqlite_temp_master` for {lit}`sqlite_temp_master` and {lit}`sqlite_temp_schema`.
SQLite finds these tables under every name, so DROP TABLE of one of them is its
{name}`PrepareError.tableMayNotBeDropped`, also with {lit}`IF EXISTS`. -/
def schemaTableName? (name : Identifier) : Option Identifier :=
  if name.sameName (name! "sqlite_master") || name.sameName (name! "sqlite_schema") then some (name! "sqlite_master")
  else if name.sameName (name! "sqlite_temp_master") || name.sameName (name! "sqlite_temp_schema") then
    some (name! "sqlite_temp_master")
  else none

/-- The position of the index with the name, or none when the name is no index. -/
def Catalog.findIndex (catalog : Catalog) (name : Identifier) : Option Nat :=
  match catalog.find name with
  | some (position, { entry := .index _, .. }) => some position
  | some (_, { entry := .table _, .. }) | some (_, { entry := .view _, .. })
  | some (_, { entry := .trigger _, .. }) | none => none

/-- Whether the name begins with {lit}`sqlite_autoindex_`, with ASCII case ignored: the
prefix of the names that SQLite gives the indexes of UNIQUE and PRIMARY KEY constraints,
which the catalog does not name. -/
def constraintIndexName (name : Identifier) : Bool := (bytes! "sqlite_autoindex_").isPrefixOf name.folded

/-- Resolve DROP TABLE: a schema table is {name}`PrepareError.tableMayNotBeDropped`; a
table drops with its indexes ({name}`Catalog.tableObjects`); a name that is no table, also
the name of an index, is {name}`PrepareError.noSuchTable`, and with {lit}`IF EXISTS` a DROP
of nothing. An unexpanded view is restricted, including with IF EXISTS. For example, {lit}`DROP TABLE IF EXISTS x` of a catalog without {lit}`x` is
{lean}`Resolved.Statement.drop []`. -/
def resolveDropTable (catalog : Catalog) (name : Identifier) (ifExists : Bool) : StatementResolution :=
  match schemaTableName? name with
  | some reported => prepareError catalog (.tableMayNotBeDropped reported)
  | none => match catalog.findTable name with
    | some (position, _) =>
      let positions := catalog.tableObjects position
      .ok (.drop positions, catalog.drop positions)
    | none => if (catalog.findView name).isSome then restrict [0] .subqueryHere
      else if ifExists then .ok (.drop [], catalog.drop []) else prepareError catalog (.noSuchTable name)

/-- Resolve DROP INDEX: an index drops alone; a name that is no index, also the name of a
table, is {name}`PrepareError.noSuchIndex`, and with {lit}`IF EXISTS` a DROP of nothing. The
catalog does not name the indexes of UNIQUE and PRIMARY KEY constraints, which SQLite
refuses to drop, so another name of their form ({name}`constraintIndexName`) is
{name}`RestrictionKind.dropConstraintIndex`. -/
def resolveDropIndex (catalog : Catalog) (name : Identifier) (ifExists : Bool) :
    StatementResolution :=
  match catalog.findIndex name with
  | some position => .ok (.drop [position], catalog.drop [position])
  | none =>
    if constraintIndexName name then restrict [0] .dropConstraintIndex
    else if ifExists then .ok (.drop [], catalog.drop [])
    else prepareError catalog (.noSuchIndex name)

end Belay.Sqlite.Model
