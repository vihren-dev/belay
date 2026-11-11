import Belay.Sqlite.Model.Schema.Rows.KeysUniqueRowEngine
import Belay.Sqlite.Model.Schema.Writes.KeysUniqueWrites
import Belay.Sqlite.Model.Schema.Ddl.KeysUniqueCreate
import Belay.Sqlite.Model.Schema.Rows.KeysUniqueAddColumn
import Belay.Sqlite.Model.Schema.Ddl.StatementDropColumn
import Belay.Sqlite.Model.Schema.Ddl.DropColumnValidLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The condition of the statement on the database for the atom "keys unique":
* ADD COLUMN: {name}`Database.AddColumnCondition` at its table;
* DROP: {name}`Catalog.DropCondition` of the catalog at its positions;
* every other statement: nothing. -/
def Resolved.Statement.KeysCondition (database : Database) : Resolved.Statement → Prop
  | .addColumn target _ _ => database.AddColumnCondition target
  | .drop positions _ => database.catalog.DropCondition positions
  | .createTable .. | .createView .. | .createIndex .. | .createTrigger .. | .rewrite _ | .dropColumn .. | .begin | .commit | .rollback | .insert .. | .update ..
  | .upsert .. | .insertSelect .. | .delete .. | .prepareError _ | .query .. | .setting _ _ => True

/-- For every rules, clock value, target, work, database, flag and algorithm: if the database
satisfies {name}`Database.KeysUnique`, the effect of {name}`rowsKeys` satisfies
{name}`Effect.Satisfies` for {name}`Database.KeysUnique`. Proof sketch: {name}`rowsKeys_keysUnique`. -/
theorem rowsKeys_effect_keysUnique (rules : Resolved.WriteRules) (clock : Int) (target : Nat) (work : RowWork)
    {database : Database} (unique : database.KeysUnique) (plain : Bool) (algorithm : Option ConflictAlgorithm) :
    (rowsKeys rules clock target work database plain algorithm).effect.Satisfies Database.KeysUnique :=
  Effect.satisfies_of_effectDatabase (rowsKeys_keysUnique rules clock target work unique plain algorithm)

end Belay.Sqlite.Model
