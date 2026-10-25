import Belay.Sqlite.MigrationPatternLaws

set_option doc.verso true

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- Success from the supplied execution inputs means every raw or concrete branch
returns and has an error-free new trace. Earlier trace errors impose no condition.
Proof sketch: apply the existing success/check bridge at an empty observation prefix. -/
theorem Sql.succeedsFrom_iff_branches {α : Type} (program : Sql α)
    (clock : Option Clock) (index : Nat) (connection : Connection) :
    program.SucceedsFrom clock index connection ↔
      ∀ result, program.Branch clock index connection result →
        result.value.isSome = true ∧ result.outputs.allOk = true := by
  let state : ExecutionContext := ⟨clock, index, connection, []⟩
  constructor
  · intro success result branch
    have checked := (program.check_allOk_iff state).mpr ⟨rfl, success⟩
    have holds := checked result branch
    cases returned : result.value with
    | none => simp [returned] at holds
    | some value =>
      refine ⟨rfl, ?_⟩
      simpa only [returned, state, ExecutionContext.finish, List.nil_append] using holds
  · intro success
    apply ((program.check_allOk_iff state).mp ?_).2
    intro result branch
    obtain ⟨returned, ok⟩ := success result branch
    cases value : result.value with
    | none => simp [value] at returned
    | some value => simpa only [value, state, ExecutionContext.finish, List.nil_append] using ok

/-- A bind succeeds exactly when its prefix succeeds and every returning prefix branch
has a successful continuation at its raw reached connection and index. The starting
trace is irrelevant to success. Proof sketch: split all bind branches; an actual tail
branch detects prefix errors, and concatenated error-free traces give both directions. -/
theorem Sql.succeedsFrom_bind_iff {α β : Type} (program : Sql α) (next : α → Sql β)
    (clock : Option Clock) (index : Nat) (connection : Connection) :
    (program.bind next).SucceedsFrom clock index connection ↔
      program.SucceedsFrom clock index connection ∧
        ∀ first, program.Branch clock index connection first → ∀ value,
          first.value = some value →
            (next value).SucceedsFrom clock (index + first.outputs.length) first.connection := by
  simp only [Sql.succeedsFrom_iff_branches]
  constructor
  · intro success
    have beforeRun (first : SqlRun α) (branch : program.Branch clock index connection first) : first.value.isSome = true ∧ first.outputs.allOk = true := by
      cases returned : first.value with
      | none =>
        have impossible := (success _ (branch.bind_stopped returned next)).1
        simp at impossible
      | some value =>
        have whole := success _ (branch.bind_return returned next (Sql.Branch.actual (next value) _ _ _))
        have ok : first.outputs.allOk = true ∧
            ((next value).runFrom clock (index + first.outputs.length) first.connection).outputs.allOk = true := by
          simpa only [List.allOk, List.all_append, Bool.and_eq_true] using whole.2
        exact ⟨rfl, ok.1⟩
    refine ⟨beforeRun, ?_⟩
    intro first branch value returned last later
    have whole := success _ (branch.bind_return returned next later)
    exact ⟨whole.1, (by simpa only [List.allOk, List.all_append, Bool.and_eq_true] using whole.2 :
      first.outputs.allOk = true ∧ last.outputs.allOk = true).2⟩
  · rintro ⟨beforeRun, tails⟩ result branch
    obtain ⟨first, before, continuation⟩ := (Sql.branch_bind_iff program next _ _ _ result).mp branch
    obtain ⟨returned, ok⟩ := beforeRun first before
    cases returnedValue : first.value with
    | none => simp [returnedValue] at returned
    | some value =>
      simp only [returnedValue] at continuation
      obtain ⟨last, later, rfl⟩ := continuation
      have tail := tails first before value returnedValue last later
      exact ⟨tail.1, by simpa [List.allOk, List.all_append] using And.intro ok tail.2⟩

/-- Quiet projection of a branch with an error-free trace is empty. The branch premise
ensures the trace belongs to this program; arbitrary unmatched trace suffixes are not
silently discarded. Proof sketch: branch induction removes each successful selected step. -/
theorem Sql.View.project_quiet_of_allOk {α : Type} {program : Sql α} {clock index connection result}
    (branch : program.Branch clock index connection result) (ok : result.outputs.allOk = true) :
    (quiet program).project result.outputs = [] := by
  induction branch with
  | pure => rfl
  | stopped => simp [List.allOk, Output.endsRun] at ok
  | @continued statement values rest clock index connection actual next selected result step choice later hypothesis =>
    have parts : selected.isError = false ∧ selected.endsRun = false ∧ result.outputs.allOk = true := by
      simpa [List.allOk, Bool.and_eq_true, and_assoc] using ok
    simp only [quiet, uniform, project, parts.1, parts.2.1, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
    exact hypothesis parts.2.2

end Belay.Sqlite
