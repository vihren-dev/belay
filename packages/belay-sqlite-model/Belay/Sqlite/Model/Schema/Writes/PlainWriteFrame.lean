import Belay.Sqlite.Model.Schema.Writes.PlainInsertEffect

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The target table position of a plain write: a resolved INSERT, UPDATE or DELETE without rules for
triggers and foreign keys. Any other statement, including a write with rules, has none. For example, a
write with a trigger can change a second table, so it has no plain target. -/
def Resolved.Statement.plainWriteTarget : Resolved.Statement → Option Nat
  | .insert target _ _ _ none | .update target _ _ _ _ none | .delete target _ _ _ none => some target
  | .insert _ _ _ _ (some _) | .update _ _ _ _ _ (some _) | .delete _ _ _ _ (some _) => none
  | .createView .. | .createTable .. | .createIndex .. | .createTrigger .. | .addColumn .. | .rewrite _ | .dropColumn .. | .drop .. | .begin
  | .commit | .rollback | .insertSelect .. | .upsert .. | .prepareError _ | .query .. | .setting .. => none

/-- For every database, target, keys, table, supplied rows and result table: a failed write of the
result gives an error that keeps the input database and has the reason
{name}`ExecutionError.constraintViolation` or {name}`ExecutionError.datatypeMismatch`. Proof sketch:
unfold {name}`insertOutcome` and {name}`checkedWrite`; every failing branch states its reason. -/
theorem insertOutcome_error {database : Database} {target : Nat} {keys : List UniqueKey}
    {table : Table} {rows : List (List Value)} {result : Table} {reason : ExecutionError} {reached : Database}
    (failed : insertOutcome database target keys table rows result = .error (reason, reached)) :
    reached = database ∧ (reason = .constraintViolation ∨ reason = .datatypeMismatch) := by
  unfold insertOutcome at failed
  split at failed
  · dsimp only at failed
    split at failed <;> cases failed <;> simp
  · unfold checkedWrite at failed
    split at failed
    · cases failed
    · cases failed; simp

/-- For every database, target, keys and result table: a failed checked write keeps the input database
and has the reason {name}`ExecutionError.constraintViolation`. Proof sketch: unfold
{name}`checkedWrite`. -/
theorem checkedWrite_error {database : Database} {target : Nat} {keys : List UniqueKey} {result : Table}
    {reason : ExecutionError} {reached : Database}
    (failed : checkedWrite database target keys result = .error (reason, reached)) :
    reached = database ∧ reason = .constraintViolation := by
  unfold checkedWrite at failed
  split at failed
  · cases failed
  · cases failed; simp

end Belay.Sqlite.Model
