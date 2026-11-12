import Belay.Sqlite.Model.Schema.Columns.RowLocalAddColumn

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The condition of a statement on the database for the atom "not null":
* ADD COLUMN: the rows of the table at its target are wide ({name}`Database.RowsWideAt`);
* every other statement: nothing. -/
def Resolved.Statement.NotNullCondition (database : Database) : Resolved.Statement → Prop
  | .addColumn target _ _ => database.RowsWideAt target
  | .createTable .. | .createView .. | .createIndex .. | .createTrigger .. | .rewrite _ | .dropColumn .. | .drop .. | .begin | .commit | .rollback | .insert ..
  | .update .. | .upsert .. | .insertSelect .. | .delete .. | .prepareError _ | .query .. | .setting _ _ => True

/-- The condition of a statement on the database for the atom "types fit":
* ADD COLUMN: the rows of the table at its target are wide ({name}`Database.RowsWideAt`), and the
  stored default of its column fits the strict type when the table has rows
  ({name}`Database.StrictDefaultFitsAt`);
* every other statement: nothing. -/
def Resolved.Statement.TypesFitCondition (database : Database) : Resolved.Statement → Prop
  | .addColumn target column _ => database.RowsWideAt target ∧ database.StrictDefaultFitsAt target column
  | .createTable .. | .createView .. | .createIndex .. | .createTrigger .. | .rewrite _ | .dropColumn .. | .drop .. | .begin | .commit | .rollback | .insert ..
  | .update .. | .upsert .. | .insertSelect .. | .delete .. | .prepareError _ | .query .. | .setting _ _ => True

/-- The condition of a statement on the database for the atom "checks hold":
* ADD COLUMN: the rows of the table at its target are wide ({name}`Database.RowsWideAt`), and each
  CHECK constraint of the table reads only columns below its width
  ({name}`Database.ChecksReadBelowAt`);
* every other statement: nothing. -/
def Resolved.Statement.ChecksHoldCondition (database : Database) : Resolved.Statement → Prop
  | .addColumn target _ _ => database.RowsWideAt target ∧ database.ChecksReadBelowAt target
  | .createTable .. | .createView .. | .createIndex .. | .createTrigger .. | .rewrite _ | .dropColumn .. | .drop .. | .begin | .commit | .rollback | .insert ..
  | .update .. | .upsert .. | .insertSelect .. | .delete .. | .prepareError _ | .query .. | .setting _ _ => True

end Belay.Sqlite.Model
