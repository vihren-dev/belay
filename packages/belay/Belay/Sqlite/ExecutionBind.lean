import Belay.Sqlite.ExecutionBranchLaws

set_option doc.verso true

namespace Belay.Sqlite
open Model

/-- For every stopped prefix branch and continuation, bind has the same stopped result.
No continuation statement runs. Proof sketch: induction on the prefix branch preserves
its outputs; a pure prefix cannot have no value. -/
theorem Sql.Branch.bind_stopped {α β : Type} {program : Sql α} {clock index connection first}
    (branch : program.Branch clock index connection first) (stopped : first.value = none)
    (next : α → Sql β) : (program.bind next).Branch clock index connection { first with value := none } := by
  induction branch with
  | pure => cases stopped
  | stopped step => exact .stopped step
  | @continued statement values rest clock index connection actual state others found selected result step member choice _ later =>
    exact Sql.Branch.continued (rest := fun output => (rest output).bind next)
      (result := { result with value := none }) step member choice (later stopped)

/-- For every returning prefix branch and continuation branch from its exact reached
connection and next index, bind permits their concatenated result. The same clock is used
throughout. Proof sketch: induction on the prefix branch adds its outputs in order. -/
theorem Sql.Branch.bind_return {α β : Type} {program : Sql α} {clock index connection first}
    (branch : program.Branch clock index connection first) {value : α} (returned : first.value = some value)
    (next : α → Sql β) {last : SqlRun β}
    (later : (next value).Branch clock (index + first.outputs.length) first.connection last) :
    (program.bind next).Branch clock index connection
      { last with outputs := first.outputs ++ last.outputs } := by
  induction branch with
  | pure => cases returned; simpa [Sql.bind] using later
  | stopped => cases returned
  | @continued statement values rest clock index connection actual state others found selected result step member choice _ hypothesis =>
    exact Sql.Branch.continued (rest := fun output => (rest output).bind next)
      (result := { last with outputs := result.outputs ++ last.outputs }) step member choice
      (hypothesis returned (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using later))

/-- Every bind branch splits into a prefix branch and its exact continuation behavior.
A stopped prefix gives the stopped result alone. A returning prefix permits every branch
of the continuation at its reached connection and advanced index, with traces concatenated.
Proof sketch: induction on the first program inverts its first execution step. -/
theorem Sql.branch_bind_iff {α β : Type} (program : Sql α) (next : α → Sql β) :
    ∀ clock index connection (result : SqlRun β),
      (program.bind next).Branch clock index connection result ↔
        ∃ first, program.Branch clock index connection first ∧
          match first.value with
          | none => result = { first with value := none }
          | some value => ∃ last, (next value).Branch clock (index + first.outputs.length) first.connection last ∧
              result = { last with outputs := first.outputs ++ last.outputs } := by
  induction program with
  | pure value =>
    intro clock index connection result
    simp [Sql.bind, Sql.branch_pure_iff]
  | exec statement values rest hypothesis =>
    intro clock index connection result
    constructor
    · intro branch
      cases step : runScriptStep runContext clock index connection statement values with
      | ended reason =>
        have same := (Sql.branch_stopped_iff step result).mp branch
        exact ⟨_, .stopped step, same⟩
      | continued actual state others =>
        obtain ⟨selected, after, choice, tail, rfl⟩ := (Sql.branch_continued_iff step result).mp branch
        obtain ⟨first, before, continuation⟩ := (hypothesis selected clock (index + 1) state after).mp tail
        refine ⟨{ first with outputs := selected :: first.outputs }, .continued_own step choice before, ?_⟩
        cases returned : first.value with
        | none =>
          simp only [returned] at continuation ⊢
          cases continuation; rfl
        | some value =>
          simp only [returned] at continuation ⊢
          obtain ⟨last, nextBranch, rfl⟩ := continuation
          exact ⟨last, by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using nextBranch, rfl⟩
    · rintro ⟨first, before, continuation⟩
      cases returned : first.value with
      | none =>
        simp only [returned] at continuation
        cases continuation
        exact before.bind_stopped returned next
      | some value =>
        simp only [returned] at continuation
        obtain ⟨last, nextBranch, rfl⟩ := continuation
        exact before.bind_return returned next nextBranch

end Belay.Sqlite
