import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyStatement

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Sufficient conditions for a resolved statement to keep the parent schemas of a database
compatible with the selected mapping:
* CREATE, also CREATE VIEW, requires that every old declaration keeps its selected parent
  ({name}`Catalog.CreateKeepsSelection`). CREATE TABLE also requires a located parent for every
  new declaration ({name}`Catalog.CreateLocatesNewKeys`).
* ADD COLUMN requires the same for the column ({name}`Catalog.AddColumnKeepsSelection`,
  {name}`Catalog.AddColumnLocatesNewKeys`).
* DROP, with or without rules, requires that every kept declaration keeps its selected parent,
  moved ({name}`Catalog.DropKeepsSelection`).
* DROP COLUMN requires nothing: the run stores the new catalog only when it keeps
  the outline and the selected parents of the catalog after the drop, and no foreign key names the column.
* A rewrite of the catalog by a rename requires that the renamed catalog selects the same parents as the old one
  ({name}`Catalog.selectedParents`). The run stores the new catalog only when it keeps the outline, which does not
  imply this.
* Every other form keeps the catalog and requires nothing, whatever the rows and enforcement. -/
def Resolved.Statement.ForeignKeySchemaCondition (database : Database) : Resolved.Statement → Prop
  | .createTable _ name shape => database.catalog.CreateKeepsSelection {name, entry := .table shape} ∧
      database.catalog.CreateLocatesNewKeys {name, entry := .table shape}
  | .createIndex _ name index => database.catalog.CreateKeepsSelection {name, entry := .index index}
  | .createTrigger _ name trigger => database.catalog.CreateKeepsSelection {name, entry := .trigger trigger}
  | .createView _ name view => database.catalog.CreateKeepsSelection {name, entry := .view view}
  | .addColumn target column _ => database.catalog.AddColumnKeepsSelection target column ∧
      database.catalog.AddColumnLocatesNewKeys target column
  | .drop positions _ => database.catalog.DropKeepsSelection positions
  | .begin | .commit | .rollback | .insert .. | .update .. | .upsert .. | .insertSelect .. | .delete ..
  | .prepareError _ | .query .. | .setting _ _ | .dropColumn .. => True
  | .rewrite renamed => renamed.selectedParents = database.catalog.selectedParents

/-- Sufficient conditions for a resolved statement to keep both atoms under the selected mapping:
* CREATE TABLE requires a located parent for every new declaration
  ({name}`Catalog.CreateLocatesNewKeys`); CREATE VIEW, CREATE INDEX and CREATE TRIGGER require nothing.
  The input atoms give the selection of every old declaration.
* ADD COLUMN requires {name}`Database.AddColumnRowsCondition` and a located parent for every
  declaration of the column ({name}`Catalog.AddColumnLocatesNewKeys`).
* DROP requires that every kept declaration keeps its selected parent, moved, and its located
  parents ({name}`Catalog.DropKeepsSelection`, {name}`Catalog.DropKeepsParents`). DROP with rules
  also requires admission, unique keys and the FK rule conditions of its implicit DELETE.
* A rewrite of the catalog by a rename requires that every foreign key keeps its selected parent
  ({name}`Catalog.selectedParents`). A DROP COLUMN requires nothing.
* Every other form requires {name}`Resolved.Statement.ForeignKeyRowsCondition`.
For a removed referenced parent, which only the row atom survives, use the individual laws. -/
def Resolved.Statement.ForeignKeyAtomsCondition (profile : Profile) (database : Database) :
    Resolved.Statement → Prop
  | .createTable _ name shape => database.catalog.CreateLocatesNewKeys {name, entry := .table shape}
  | .createIndex .. | .createTrigger .. | .createView .. => True
  | .addColumn target column refuses => database.AddColumnRowsCondition target column refuses ∧
      database.catalog.AddColumnLocatesNewKeys target column
  | .drop positions none => database.catalog.DropKeepsSelection positions ∧ database.catalog.DropKeepsParents positions
  | .drop positions (some rules) => database.ForeignKeyReady profile ∧
      rules.ForeignKeyConditions profile database.catalog ∧
      database.catalog.DropKeepsSelection positions ∧ database.catalog.DropKeepsParents positions
  | statement@(.insert ..) | statement@(.update ..) | statement@(.upsert ..) | statement@(.insertSelect ..) | statement@(.delete ..)
  | statement@.begin | statement@.commit | statement@.rollback | statement@(.prepareError _) | statement@(.rewrite _) | statement@(.dropColumn ..)
  | statement@(.query ..) | statement@(.setting _ _) => statement.ForeignKeyRowsCondition profile database

end Belay.Sqlite.Model
