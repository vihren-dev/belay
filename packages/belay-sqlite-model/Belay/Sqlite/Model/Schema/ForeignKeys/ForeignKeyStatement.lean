import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyPlainFrame
import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyDdlSelected
import Belay.Sqlite.Model.Schema.Ddl.StatementDropColumn
import Belay.Sqlite.Model.Schema.Ddl.DropColumnForeignFacts

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Sufficient conditions for selected row-reference preservation by a resolved statement:
* INSERT, UPSERT and DELETE with rules require admission, unique keys and FK rule conditions.
* UPDATE with rules also requires structural assignment conditions.
* Those four plain forms without rules require a target outside every FK child/parent read.
* Queries, settings, preparation errors and transaction controls require nothing here.
* CREATE, also CREATE VIEW, requires that every old declaration keeps its selected parent
  ({name}`Catalog.CreateKeepsSelection`). New declarations have no rows to check. A view has no
  rows and no declarations.
* A rewrite of the catalog by a rename requires that every foreign key keeps its selected parent
  ({name}`Catalog.selectedParents`): the run stores the new catalog only when it keeps the outline, and the
  rows then find their parents again. A rename that makes a key find a parent that it did not find before
  (the key named the new name of the table) is outside this condition, as a CREATE TABLE of that name is.
* DROP COLUMN requires nothing: the run drops the cells only when the stored catalog has the outline and the
  selected parents of the catalog after the drop, and the dropped column is none that a foreign key names
  ({name}`Catalog.droppable`).
* ADD COLUMN requires {name}`Database.AddColumnRowsCondition`.
* DROP without rules requires that every kept declaration keeps its selected parent, moved, and its
  located parents ({name}`Catalog.DropKeepsSelection`, {name}`Catalog.DropKeepsParents`).
* DROP with rules requires admission, unique keys, the FK rule conditions of its implicit DELETE
  and {name}`Database.EnforcedDropFrames`.
Rule-based UPSERT DO UPDATE still has its current undescribed result; this condition does not
promise successful execution of that branch. -/
def Resolved.Statement.ForeignKeyRowsCondition (profile : Profile) (database : Database) : Resolved.Statement → Prop
  | .insert target _ _ _ rules | .upsert target _ _ _ _ _ rules | .insertSelect target _ _ _ _ _ _ rules | .delete target _ _ _ rules =>
      match rules with
      | none => database.catalog.ForeignKeyOutside target
      | some rules => database.ForeignKeyReady profile ∧ rules.ForeignKeyConditions profile database.catalog
  | .update target assignments _ _ _ rules =>
      match rules with
      | none => database.catalog.ForeignKeyOutside target
      | some rules => database.ForeignKeyReady profile ∧ rules.ForeignKeyConditions profile database.catalog ∧
          ForeignKeyAssignmentConditions database.catalog target assignments
  | .begin | .commit | .rollback | .query .. | .prepareError _ | .setting .. | .dropColumn .. => True
  | .rewrite renamed => renamed.selectedParents = database.catalog.selectedParents
  | .createTable _ name shape => database.catalog.CreateKeepsSelection {name, entry := .table shape}
  | .createIndex _ name index => database.catalog.CreateKeepsSelection {name, entry := .index index}
  | .createTrigger _ name trigger => database.catalog.CreateKeepsSelection {name, entry := .trigger trigger}
  | .createView _ name view => database.catalog.CreateKeepsSelection {name, entry := .view view}
  | .addColumn target column refuses => database.AddColumnRowsCondition target column refuses
  | .drop positions none => database.catalog.DropKeepsSelection positions ∧ database.catalog.DropKeepsParents positions
  | .drop positions (some rules) => database.ForeignKeyReady profile ∧
      rules.ForeignKeyConditions profile database.catalog ∧ database.EnforcedDropFrames rules positions

end Belay.Sqlite.Model
