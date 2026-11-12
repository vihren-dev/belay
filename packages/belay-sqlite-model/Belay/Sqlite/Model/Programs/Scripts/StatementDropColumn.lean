import Belay.Sqlite.Model.Programs.Scripts.StatementRewrite
import Belay.Sqlite.Model.Schema.Ddl.StatementRewrite
import Belay.Sqlite.Model.Schema.Ddl.DropColumnDatabaseLaws

set_option doc.verso true

/-! The run of a DROP COLUMN statement for the statement theorems (ADR 0019, D4). The statement
({lit}`Resolved.Statement.dropColumn`) either drops the cells of the column and stores the catalog of the
statement, when {lit}`Database.runsDropColumn` holds, or fails as {lit}`ExecutionError.unmodeled` and keeps
the database. A theorem about all statements needs one case for it, and these contracts give it without
unfolding {lit}`step`. -/

namespace Belay.Sqlite.Model

/-- The contract of a DROP COLUMN that the model does not run: it fails as {lit}`ExecutionError.unmodeled` and
returns the database that it was given. Proof sketch: the guard of {name}`step` fails. -/
theorem step_dropColumn_of_not_runs (clock : Int) (counters : Counters) (parameters : List Value)
    {database : Database} {position index : Nat} {stored : Catalog}
    (rejected : database.runsDropColumn position index stored = false) :
    step clock counters parameters (.dropColumn position index stored) database = .error (.unmodeled, database) := by
  simp [step, rejected]

/-- What a successful run of a DROP COLUMN tells: the model ran it ({name}`Database.runsDropColumn`), and the result
is {name}`Database.dropColumn`. Proof sketch: case split on the guard of {name}`step`. -/
theorem step_dropColumn_ok (clock : Int) (counters : Counters) (parameters : List Value)
    {database after : Database} {position index : Nat} {stored : Catalog}
    (ran : step clock counters parameters (.dropColumn position index stored) database = .ok after) :
    database.runsDropColumn position index stored = true ∧ after = database.dropColumn position index stored := by
  cases runs : database.runsDropColumn position index stored
  · simp [step, runs] at ran
  · simp [step, runs] at ran
    exact ⟨rfl, ran.symm⟩

end Belay.Sqlite.Model
