import Belay

set_option doc.verso true

/-! Client observation of the first write-rule kind in ADR 0033, slice 7. -/

namespace InsertWithRulesClaim
open Belay.Sqlite Model

/-- For any valid database and modeled INSERT with write rules and no RETURNING, the program
receives the change count or a primary error and records that result in the trace.
Proof sketch: the two continuing cases of the INSERT rule give the count and the refusal. -/
theorem inserted_count_or_error (ctx : ExecutionContext) (stmt : Syntax.Statement) (parameters : List Value)
    (target : Nat) (rows : List (List Resolved.Cell)) (subqueries : List Resolved.Query)
    (rules : Resolved.WriteRules) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt =
      .ok (.insert target rows [] subqueries (some rules), after))
    (modeled : (runScriptStep runContext ctx.clock ctx.index ctx.connection stmt parameters).continues = true) :
    (send ⟨[(stmt, parameters)]⟩).check (fun outputs final =>
      ((∃ changes, outputs = [.done changes]) ∨ (∃ code, outputs = [.error code])) ∧
        final.outputs = ctx.outputs ++ outputs) ctx := by
  sql_run [found, modeled]
  all_goals first | exact ⟨Or.inl ⟨_, rfl⟩, rfl⟩ | exact ⟨Or.inr ⟨_, rfl⟩, rfl⟩

#print axioms inserted_count_or_error

end InsertWithRulesClaim
