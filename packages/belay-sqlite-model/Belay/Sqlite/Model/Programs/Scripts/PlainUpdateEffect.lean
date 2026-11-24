import Belay.Sqlite.Model.Programs.Scripts.SuccessfulScriptEffects
import Belay.Sqlite.Model.Programs.Scripts.KeysUniqueWrites
import Belay.Sqlite.Model.Schema.Writes.PlainInsertEffect
import Belay.Sqlite.Model.Programs.Scripts.StepRuleProjections
import Belay.Sqlite.Model.Schema.Writes.PlainWriteFrame

set_option doc.verso true

/-! A successful UPDATE without write rules stores the computed rows. -/

namespace Belay.Sqlite.Model
open Resolved

/-- For every present table, assignment list, filter, returning list and
subquery list, a successful UPDATE without a foreign-key or trigger plan
stores exactly the rows computed by {name}`LiteralData.updated`. This states
the effect only; it does not assert that the statement passes its support
check or succeeds on every database. Proof sketch: success excludes the
alias-mismatch and constraint-failure branches, leaving the stored row list. -/
theorem runStatement_update_ok (clock : Int) (counters : Counters) (parameters : List Value)
    {database after : Database} {target : Nat} {table : Table}
    (assignments : List (Nat × Expr)) (filter : Option Expr)
    (returning : List (Expr × String)) (subqueries : List Query)
    (present : database.table target = some table)
    (success : (runStatement clock counters parameters
      (.update target assignments filter returning subqueries none) database).effect = .ok after) :
    after = database.setRows target
      (LiteralData.updated (statementContext clock counters parameters database subqueries)
        table assignments filter).rows := by
  exact updateOutcome_ok (by simpa only [runStatement, present, Option.map_none, StatementRun.withKeys] using success)

/-- Under the successful plain UPDATE assumptions of {name}`runStatement_update_ok`,
if the target has a storage slot, its resulting table is exactly the computed
updated table, including its unchanged schema. Proof sketch: the exact effect
stores those rows, and {name}`Database.table_setRows` identifies the table. -/
theorem table_after_update_ok (clock : Int) (counters : Counters) (parameters : List Value)
    {database after : Database} {target : Nat} {table : Table}
    (assignments : List (Nat × Expr)) (filter : Option Expr)
    (returning : List (Expr × String)) (subqueries : List Query)
    (present : database.table target = some table) (aligned : target < database.rows.length)
    (success : (runStatement clock counters parameters
      (.update target assignments filter returning subqueries none) database).effect = .ok after) :
    after.table target = some
      (LiteralData.updated (statementContext clock counters parameters database subqueries)
        table assignments filter) := by
  rw [runStatement_update_ok clock counters parameters assignments filter returning subqueries present success]
  exact Database.table_setRows _ present aligned

end Belay.Sqlite.Model
