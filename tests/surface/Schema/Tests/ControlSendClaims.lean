import Belay

set_option doc.verso true

/-! Client claims about failed transaction commands and successful setting pragmas on variable databases. -/

namespace ControlSendClaims
open Belay.Sqlite Model

/-- For every valid connection, sending BEGIN inside a transaction reports an error and keeps the connection.
Proof sketch: the resolution and transaction state select a continuing case of the kind rule. -/
theorem begin_failure (ctx : ExecutionContext) (original : Model.Database)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (snapshot : ctx.connection.state.snapshot = some original) :
    (send (sql r"BEGIN")).check
      (fun outputs final => outputs = [.error 1] ∧ final.connection = ctx.connection) ctx := by
  sql_run [rfl, snapshot]
  all_goals first | exact ⟨rfl, rfl⟩ | simp [rule, snapshot, RunStep.continues]

#print axioms begin_failure

/-- For every valid connection, sending COMMIT outside a transaction reports an error and keeps the connection.
Proof sketch: the resolution and transaction state select a continuing case of the kind rule. -/
theorem commit_failure (ctx : ExecutionContext)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (snapshot : ctx.connection.state.snapshot = none) :
    (send (sql r"COMMIT")).check
      (fun outputs final => outputs = [.error 1] ∧ final.connection = ctx.connection) ctx := by
  sql_run [rfl, snapshot]
  all_goals first | exact ⟨rfl, rfl⟩ | simp [rule, snapshot, RunStep.continues]

#print axioms commit_failure

/-- For every valid connection, sending ROLLBACK outside a transaction reports an error and keeps the connection.
Proof sketch: the resolution and transaction state select a continuing case of the kind rule. -/
theorem rollback_failure (ctx : ExecutionContext)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (snapshot : ctx.connection.state.snapshot = none) :
    (send (sql r"ROLLBACK")).check
      (fun outputs final => outputs = [.error 1] ∧ final.connection = ctx.connection) ctx := by
  sql_run [rfl, snapshot]
  all_goals first | exact ⟨rfl, rfl⟩ | simp [rule, snapshot, RunStep.continues]

#print axioms rollback_failure

/-- For every valid connection, sending the recursive-triggers pragma turns the setting on and keeps the database.
Proof sketch: the resolution and transaction state select a continuing case of the kind rule. -/
theorem setting_keeps_database (ctx : ExecutionContext)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned)) :
    (send (sql r"PRAGMA recursive_triggers = ON")).check
      (fun _ final => final.connection.recursiveTriggers = true ∧ final.connection.state.database = ctx.connection.state.database) ctx := by
  sql_run [rfl]
  exact ⟨rfl, rfl⟩

#print axioms setting_keeps_database

end ControlSendClaims
