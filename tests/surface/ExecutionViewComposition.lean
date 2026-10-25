import MigrationComposition

set_option doc.verso true
set_option maxRecDepth 8192

namespace MigrationCompositionExamples
open Belay.Sqlite Belay.Sqlite.Model ExecutionViewComparisonExamples

/-- A different hidden row still returns the same application value in one raw step. -/
def another : Sql Nat :=
  let (statement, values) := (sql r"SELECT 2").statements[0]
  .exec statement values fun _ => .pure 7

/-- The second prefix has exactly one branch with its different hidden raw output.
Proof sketch: invert the deterministic step and pure continuation. -/
theorem another_unique (result : SqlRun Nat) :
    another.Branch initial.clock initial.index initial.connection result ↔
      result = { outputs := [.rows [[2]]], connection := initial.connection, value := some 7 } := by
  have step : let (statement, values) := (sql r"SELECT 2").statements[0]
      runScriptStep runContext initial.clock initial.index initial.connection statement values =
        .continued (.rows [[2]]) initial.connection := rfl
  constructor
  · intro branch
    obtain ⟨selected, later, choice, tail, rfl⟩ := (Sql.branch_continued_iff step result).mp branch
    have selectedEq : selected = .rows [[2]] := by simpa [OutputChoice] using choice
    subst selected
    have laterEq := (Sql.branch_pure_iff 7 _ _ _ later).mp tail
    subst later
    rfl
  · rintro rfl
    exact .continued (rest := fun _ => .pure 7) step (.actual _) (.pure 7 _ _ _)

/-- Quiet prefixes compare fully despite different raw traces. Both connections, raw
counts and returned values agree. Proof sketch: classify the two deterministic branches. -/
theorem quiet_prefixes : (Sql.View.quiet one).EquivAt (Sql.View.quiet another) initial := by
  constructor
  · rfl
  · intro observed
    change (∃ result, one.Branch initial.clock initial.index initial.connection result ∧ _) ↔
      (∃ result, another.Branch initial.clock initial.index initial.connection result ∧ _)
    simp only [one_unique, another_unique, exists_eq_left]
    rfl

/-- A trace-sensitive continuation domain holds on the left raw context but on neither
its projected context nor the right raw context. This prevents silently substituting
projected reachability for raw ReturnsIn. -/
theorem trace_domains_differ :
    let left := one.runFrom initial.clock initial.index initial.connection
    let right := another.runFrom initial.clock initial.index initial.connection
    (initial.finish left).outputs = [.error 1, .rows [[1]]] ∧
      ((Sql.View.quiet one).finish initial left).outputs ≠ [.error 1, .rows [[1]]] ∧
      (initial.finish right).outputs ≠ [.error 1, .rows [[1]]] := by decide +kernel

/-- Full bind congruence uses only the left raw trace premise, even with a different
hidden trace on the right. The continuation depends on the returned value.
Proof sketch: apply the public restricted rule and discharge raw reachability exactly. -/
theorem raw_domain_composition :
    ((Sql.View.quiet one).bind (fun value => .pure (value + 1)) (fun value => .pure (value + 1))).EquivAt
      ((Sql.View.quiet another).bind (fun value => .pure (1 + value)) (fun value => .pure (1 + value))) initial := by
  apply Sql.View.EquivOn.bind (pre := fun state => state = initial)
    (post := fun _ state => state.outputs = [.error 1, .rows [[1]]])
    (fun state equal => by subst state; exact quiet_prefixes) ?_ ?_ initial rfl
  · intro value state _
    rw [Nat.add_comm 1 value]
    exact Sql.View.EquivAt.refl (.pure (value + 1)) state
  · intro state equal result branch value returned
    subst state
    have resultEq := (one_unique _ _ result).mp branch
    subst result
    rfl

/-- Result-dependent continuations compose on every raw and concrete prefix choice,
using raw trace length for their reached domain. Proof sketch: invert the finite prefix
choices and retain the continuation's value-dependent arithmetic equality. -/
theorem all_choice_composition :
    ((Sql.View.quiet (choices false)).bind (fun value => .pure (value + 1)) (fun value => .pure (value + 1))).EquivAt
      ((Sql.View.quiet (choices false)).bind (fun value => .pure (1 + value)) (fun value => .pure (1 + value))) initial := by
  apply Sql.View.EquivOn.bind (pre := fun state => state = initial) (post := fun _ state => state.outputs.length = 2)
    (fun state _ => Sql.View.EquivAt.refl _ state) ?_ ?_ initial rfl
  · intro value state _
    rw [Nat.add_comm 1 value]
    exact Sql.View.EquivAt.refl (.pure (value + 1)) state
  · intro state equal result branch value returned
    subst state
    obtain ⟨selected, later, choice, tail, rfl⟩ := (Sql.branch_continued_iff choices_step result).mp branch
    have laterEq := (Sql.branch_pure_iff _ _ _ _ later).mp tail
    subst later
    rfl

#print axioms another_unique
#print axioms quiet_prefixes
#print axioms trace_domains_differ
#print axioms raw_domain_composition
#print axioms all_choice_composition
#print axioms Sql.View.fullObservation_eq_iff
#print axioms Sql.View.EquivAt.with_outputs
#print axioms Sql.View.ObservationEquivAt.full_of_frames
#print axioms Sql.View.full_bind_stopped_eq
#print axioms Sql.View.full_bind_return_eq
#print axioms Sql.View.EquivAt.bind_branch
#print axioms Sql.View.EquivOn.bind
#print axioms Sql.View.Equiv.bind
#print axioms Sql.View.observation_bind_return_eq
#print axioms Sql.View.observation_bind_branch
#print axioms Sql.View.ObservationEquivOn.bind_same
#print axioms Sql.View.uniform_bind
#print axioms Sql.View.project_bind_pure
#print axioms Sql.View.project_bind_assoc
#print axioms Sql.View.equiv_of_program_eq
end MigrationCompositionExamples
