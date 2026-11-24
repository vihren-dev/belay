import Belay

set_option doc.verso true

namespace Belay.Sqlite.ReplacedGeneral
open Belay.Sqlite Model

/-- The former {lit}`Sql.check_send_of_step` contract. Its hypotheses give one execution with
one output, which suffices for the common send rule. -/
theorem Sql.check_send_of_step {ctx : ExecutionContext} {statement : Syntax.Statement} {values : List Value}
    {post : List Output → ExecutionContext → Prop}
    (single : ∀ resolved after, resolveStatement runContext ctx.connection.resolveState statement =
      .ok (resolved, after) → resolved.fromQuery = false)
    (modeled : ∃ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others)
    (notChoice : ∀ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others →
        ∀ alternatives, output ≠ .oneOf alternatives)
    (reached : ∀ output next,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next [] →
        next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next))
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned)) :
    (send ⟨[(statement, values)]⟩).check post ctx := by
  obtain ⟨output, next, others, step⟩ := modeled
  obtain rfl := runScriptStep_others_of_single step single
  refine Sql.check_send_of_rule step valid rfl ?_
  intro execution member held
  obtain rfl : execution = ⟨output, next⟩ := by simpa [RunStep.executions] using member
  refine ⟨reached _ _ step held, ?_⟩
  cases output with
  | oneOf rows => exact (notChoice _ _ _ step rows rfl).elim
  | done _ | rows _ | error _ | unmodeled _ => trivial

#print axioms Sql.check_send_of_step

/-- The former {lit}`Sql.check_send_of_step_notInsertSelect` contract. The syntax hypothesis
implies that resolution gives a single execution. -/
theorem Sql.check_send_of_step_notInsertSelect {ctx : ExecutionContext} {statement : Syntax.Statement}
    {values : List Value} {post : List Output → ExecutionContext → Prop}
    (notInsertSelect : statement.isInsertSelect = false)
    (modeled : ∃ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others)
    (notChoice : ∀ output next others,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next others →
        ∀ alternatives, output ≠ .oneOf alternatives)
    (reached : ∀ output next,
      runScriptStep runContext ctx.clock ctx.index ctx.connection statement values = .continued output next [] →
        next.state.Holds (Database.Valid Profile.pinned) → post [output] (ctx.next output next))
    (valid : ctx.connection.state.Holds (Database.Valid Profile.pinned)) :
    (send ⟨[(statement, values)]⟩).check post ctx :=
  Sql.check_send_of_step (fun _ _ found => resolveStatement_single _ _ _ _ _ notInsertSelect found)
    modeled notChoice reached valid

#print axioms Sql.check_send_of_step_notInsertSelect

end Belay.Sqlite.ReplacedGeneral
