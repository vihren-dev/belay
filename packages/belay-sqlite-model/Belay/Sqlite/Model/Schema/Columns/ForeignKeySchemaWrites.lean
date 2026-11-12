import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeySchemaFrame
import Belay.Sqlite.Model.Schema.Rows.AdmittedRowsOnly

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every supplied mapping, parent-schema compatibility has the row-write laws: removing
rows or storing an admitted row preserves it. The row-admission premise is unnecessary here.
Proof sketch: both row operations retain the catalog, which is the atom's only database input. -/
theorem parentSchemasCompatibleLaws (mapping : ForeignKeyMapping) :
    WriteLaws (Database.ParentSchemasCompatible mapping) where
  sublist _ _ _ holds _ := holds.catalog_eq rfl
  write _ _ _ _ holds _ _ _ := holds.catalog_eq rfl

/-- For every supplied mapping, row work, rules and input database with compatible parent
schemas, the row engine retains that schema fact on success and partial FAIL. Other errors
require nothing of their carrier. Triggers, actions, recursion depth, enforcement and stored
rows are unrestricted. Proof sketch: use the existing row-engine preservation theorem with
{name}`parentSchemasCompatibleLaws`; all its writes retain the catalog. -/
theorem rowsKeys_parentSchemasCompatible (mapping : ForeignKeyMapping) (rules : Resolved.WriteRules)
    (clock : Int) (target : Nat) (work : RowWork) {database : Database}
    (holds : database.ParentSchemasCompatible mapping) (plain : Bool) (algorithm : Option ConflictAlgorithm) :
    (rowsKeys rules clock target work database plain algorithm).effect.Satisfies
      (Database.ParentSchemasCompatible mapping) :=
  rowsKeys_satisfies (parentSchemasCompatibleLaws mapping) rules clock target work holds plain algorithm

/-- The statement is INSERT, UPDATE, UPSERT, DELETE, a query, a setting, a preparation error
or transaction control. These forms retain the catalog, including while their triggers and
actions write rows. CREATE, ADD COLUMN, RENAME and DROP require their own schema conditions and do
not meet this sufficient condition. -/
def Resolved.Statement.KeepsParentSchema : Resolved.Statement → Prop
  | .begin | .commit | .rollback | .insert .. | .update .. | .upsert .. | .insertSelect .. | .delete ..
  | .prepareError _ | .query .. | .setting _ _ => True
  | .createTable .. | .createView .. | .createIndex .. | .createTrigger .. | .addColumn .. | .rewrite _ | .dropColumn .. | .drop .. => False

/-- Whether a statement meets the catalog-preserving condition is decidable from its form. -/
instance (statement : Resolved.Statement) : Decidable statement.KeepsParentSchema := by
  cases statement <;> simp only [Resolved.Statement.KeepsParentSchema] <;> infer_instance

end Belay.Sqlite.Model
