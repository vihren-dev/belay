import Belay.Sqlite.ExecutionViewEquivalenceLaws

set_option doc.verso true

namespace Belay.Sqlite

/-- At one starting context, full observations agree exactly when the optional value,
projected trace, complete connection and raw step count agree. The count is independent
of the projected trace length. Proof sketch: extract the context fields, cancel the
shared starting index and trace, and reconstruct the observation. -/
theorem Sql.View.fullObservation_eq_iff {α : Type} {first second : Sql α}
    (left : View first) (right : View second) (state : ExecutionContext) (one two : SqlRun α) :
    left.fullObservation state one = right.fullObservation state two ↔
      left.observation one = right.observation two ∧ one.connection = two.connection ∧
        one.outputs.length = two.outputs.length := by
  constructor
  · intro same
    refine ⟨left.observation_eq_of_full right state one two same,
      congrArg (fun seen => seen.2.connection) same, ?_⟩
    exact Nat.add_left_cancel (congrArg (fun seen => seen.2.index) same)
  · rintro ⟨observed, connection, steps⟩
    have value := congrArg Prod.fst observed
    have outputs := congrArg Prod.snd observed
    change one.value = two.value at value
    change left.project one.outputs = right.project two.outputs at outputs
    simp only [fullObservation, finish, ExecutionContext.finish]
    rw [value, connection, steps, outputs]

/-- Replacing only the starting trace preserves full projected comparison. Execution
reads the unchanged clock, index and connection. This transports a proved comparison;
it does not transport an arbitrary trace-sensitive precondition. Proof sketch: cancel
the starting trace with the full-observation characterization for actual and branch results. -/
theorem Sql.View.EquivAt.with_outputs {α : Type} {first second : Sql α}
    {left : View first} {right : View second} {state : ExecutionContext}
    (same : left.EquivAt right state) (outputs : List Output) :
    left.EquivAt right { state with outputs } := by
  refine ⟨(fullObservation_eq_iff _ _ _ _ _).mpr ((fullObservation_eq_iff _ _ _ _ _).mp same.actual), ?_⟩
  intro observed
  constructor
  · rintro ⟨result, branch, seen⟩
    obtain ⟨other, matched, equal⟩ := (same.branches _).mp ⟨result, branch, rfl⟩
    exact ⟨other, matched, ((fullObservation_eq_iff _ _ _ _ _).mpr
      ((fullObservation_eq_iff _ _ _ _ _).mp equal)).trans seen⟩
  · rintro ⟨result, branch, seen⟩
    obtain ⟨other, matched, equal⟩ := (same.branches _).mpr ⟨result, branch, rfl⟩
    exact ⟨other, matched, ((fullObservation_eq_iff _ _ _ _ _).mpr
      ((fullObservation_eq_iff _ _ _ _ _).mp equal)).trans seen⟩

/-- Weak comparison lifts to full comparison if every pair of branches with the same
weak observation also has equal complete connections and raw step counts. These are
independent execution facts, not assumptions of the target comparison. Connection
equality includes counters, settings, transaction snapshots and the stored clock
assignment; the shared external clock is preserved automatically. Catalog resolution
and clock-sensitive execution must satisfy these same facts. Proof sketch: use the
weak correspondence to select each matching branch, then add its two frame facts.
Actual runs are branches, so the same premises cover actual equality separately. -/
theorem Sql.View.ObservationEquivAt.full_of_frames {α : Type} {first second : Sql α}
    {left : View first} {right : View second} {state : ExecutionContext}
    (same : left.ObservationEquivAt right state)
    (connections : ∀ one two, first.Branch state.clock state.index state.connection one →
      second.Branch state.clock state.index state.connection two →
      left.observation one = right.observation two → one.connection = two.connection)
    (steps : ∀ one two, first.Branch state.clock state.index state.connection one →
      second.Branch state.clock state.index state.connection two →
      left.observation one = right.observation two → one.outputs.length = two.outputs.length) :
    left.EquivAt right state := by
  have complete one two before after observed := (fullObservation_eq_iff left right state one two).mpr
    ⟨observed, connections one two before after observed, steps one two before after observed⟩
  refine ⟨complete _ _ (Sql.Branch.actual first _ _ _) (Sql.Branch.actual second _ _ _) same.actual, ?_⟩
  intro observed
  constructor
  · rintro ⟨result, branch, seen⟩
    obtain ⟨other, matched, equal⟩ := (same.branches _).mp ⟨result, branch, rfl⟩
    exact ⟨other, matched, (complete _ _ branch matched equal.symm).symm.trans seen⟩
  · rintro ⟨result, branch, seen⟩
    obtain ⟨other, matched, equal⟩ := (same.branches _).mpr ⟨result, branch, rfl⟩
    exact ⟨other, matched, (complete _ _ matched branch equal).trans seen⟩

end Belay.Sqlite
