import Belay.Sqlite.ExecutionBind

set_option doc.verso true

namespace Belay.Sqlite
open Model

/-- Every complete branch returns a value satisfying the postcondition at its full reached
context. A branch that stops unmodeled makes this false. Modeled SQL errors may continue;
the postcondition decides what their trace permits. The existing output prefix is retained.
For example, a true postcondition requires only that every branch remains modeled. -/
def Sql.check {α : Type} (program : Sql α) (post : α → ExecutionContext → Prop)
    (state : ExecutionContext) : Prop :=
  ∀ result, program.Branch state.clock state.index state.connection result →
    match result.value with
    | none => False
    | some value => post value (state.finish result)

/-- A pure program checks exactly its value and unchanged context, for every postcondition.
Proof sketch: its sole branch has no outputs and keeps the connection. -/
theorem Sql.check_pure {α : Type} (value : α) (post : α → ExecutionContext → Prop)
    (state : ExecutionContext) : (Sql.pure value).check post state ↔ post value state := by
  simp [Sql.check, Sql.branch_pure_iff, ExecutionContext.finish]

/-- For every program and context, checking a conjunction is equivalent to checking both
postconditions separately. Stopped branches fail both sides.
Proof sketch: distribute conjunction through the universal branch obligation. -/
theorem Sql.check_and {α : Type} (program : Sql α) (first second : α → ExecutionContext → Prop)
    (state : ExecutionContext) : program.check (fun value state => first value state ∧ second value state) state ↔
      program.check first state ∧ program.check second state := by
  constructor
  · intro checked
    constructor
    · intro result branch; have both := checked result branch; cases returned : result.value <;> simp_all
    · intro result branch; have both := checked result branch; cases returned : result.value <;> simp_all
  · rintro ⟨firstHolds, secondHolds⟩ result branch
    have firstResult := firstHolds result branch
    have secondResult := secondHolds result branch
    cases returned : result.value <;> simp_all

/-- For every program and pointwise implication between postconditions, the first check
implies the second. Unmodeled outcomes remain forbidden.
Proof sketch: apply the implication to each returning branch. -/
theorem Sql.check_mono {α : Type} {program : Sql α} {first second : α → ExecutionContext → Prop}
    {state : ExecutionContext} (checked : program.check first state)
    (implies : ∀ value final, first value final → second value final) : program.check second state := by
  intro result branch
  have holds := checked result branch
  cases returned : result.value with
  | none => simp [returned] at holds
  | some value => exact implies value _ (by simpa [returned] using holds)

/-- For every program, continuation and context, checking bind is checking the first program
with the continuation's check as its postcondition. Every branch passes its exact reached
context. Proof sketch: the branch bind characterization splits returning prefixes and rejects
stopped prefixes; finishing the concatenated trace equals finishing its two parts. -/
theorem Sql.check_bind {α β : Type} (program : Sql α) (next : α → Sql β)
    (post : β → ExecutionContext → Prop) (state : ExecutionContext) :
    (program.bind next).check post state ↔
      program.check (fun value final => (next value).check post final) state := by
  constructor
  · intro checked first before
    cases returned : first.value with
    | none => exact checked _ (before.bind_stopped returned next)
    | some value =>
      intro last later
      have holds := checked _ (before.bind_return returned next later)
      simpa only [ExecutionContext.finish_append] using holds
  · intro checked result branch
    obtain ⟨first, before, continuation⟩ := (Sql.branch_bind_iff program next _ _ _ result).mp branch
    have holds := checked first before
    cases returned : first.value with
    | none => simp [returned] at holds
    | some value =>
      simp only [returned] at holds continuation
      obtain ⟨last, later, rfl⟩ := continuation
      simpa only [ExecutionContext.finish_append] using holds last later

/-- A checked postcondition holds for the actual execution: it returns some value, and that
value and complete reached context satisfy the postcondition. This requires no validity
assumption; validity is a separate preserved property.
Proof sketch: specialize the branch obligation to actual-run membership. -/
theorem Sql.check_actual {α : Type} {program : Sql α} {post : α → ExecutionContext → Prop}
    {state : ExecutionContext} (checked : program.check post state) :
    ∃ value, (program.runFrom state.clock state.index state.connection).value = some value ∧
      post value (state.finish (program.runFrom state.clock state.index state.connection)) := by
  have holds := checked _ (Sql.Branch.actual program _ _ _)
  cases returned : (program.runFrom state.clock state.index state.connection).value with
  | none => simp [returned] at holds
  | some value => exact ⟨value, rfl, by simpa [returned] using holds⟩

end Belay.Sqlite
