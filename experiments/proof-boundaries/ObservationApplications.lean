import ObservationAlgebra
import Belay.Sqlite.ExecutionViewFrames
import Belay.Sqlite.ExecutionDeterministic

set_option doc.verso true

namespace ProofBoundaries
open Belay.Sqlite

/-- The profile of a SQL program at its actual execution inputs, for any result observer.
Identity observes all state; a projected observer can observe less. -/
def sqlProfile {α Observation : Type} (program : Sql α) (state : ExecutionContext)
    (observe : SqlRun α → Observation) : Observation × (Observation → Prop) :=
  observationProfile (program.runFrom state.clock state.index state.connection)
    (program.Branch state.clock state.index state.connection) observe

/-- Complete SQL equivalence is equality of identity profiles. All branch results remain
observable. Proof sketch: identity images are the original branch predicates. -/
theorem full_profile_iff {α : Type} (first second : Sql α) (state : ExecutionContext) :
    first.EquivAt second state ↔ sqlProfile first state id = sqlProfile second state id := by
  rw [sqlProfile, sqlProfile, observationProfile_eq_iff]
  simp only [id_eq, exists_eq_right]
  exact ⟨fun same => ⟨same.actual, same.branches⟩, fun same => ⟨same.1, same.2⟩⟩

/-- Weak ordinary SQL equivalence is equality of value-and-trace profiles. Connection
state remains omitted. Proof sketch: the profile fields are the existing relation fields. -/
theorem weak_profile_iff {α : Type} (first second : Sql α) (state : ExecutionContext) :
    first.ObservationEquivAt second state ↔
      sqlProfile first state SqlRun.observation = sqlProfile second state SqlRun.observation := by
  rw [sqlProfile, sqlProfile, observationProfile_eq_iff]
  exact ⟨fun same => ⟨same.actual, same.branches⟩, fun same => ⟨same.1, same.2⟩⟩

/-- Full projected equivalence is equality of full-observation profiles, retaining the
connection and raw step count. Proof sketch: both compare the same actual and branch images. -/
theorem view_full_profile_iff {α : Type} {first second : Sql α}
    (left : Sql.View first) (right : Sql.View second) (state : ExecutionContext) :
    left.EquivAt right state ↔
      sqlProfile first state (left.fullObservation state) = sqlProfile second state (right.fullObservation state) := by
  rw [sqlProfile, sqlProfile, observationProfile_eq_iff]
  exact ⟨fun same => ⟨same.actual, same.branches⟩, fun same => ⟨same.1, same.2⟩⟩

/-- Weak projected equivalence is equality of projected value-and-trace profiles.
Proof sketch: both compare the same actual and branch images. -/
theorem view_weak_profile_iff {α : Type} {first second : Sql α}
    (left : Sql.View first) (right : Sql.View second) (state : ExecutionContext) :
    left.ObservationEquivAt right state ↔
      sqlProfile first state left.observation = sqlProfile second state right.observation := by
  rw [sqlProfile, sqlProfile, observationProfile_eq_iff]
  exact ⟨fun same => ⟨same.actual, same.branches⟩, fun same => ⟨same.1, same.2⟩⟩

/-- Full view equality implies weak view equality, without a new branch-matching proof.
Proof sketch: the generic transport law uses the full-observation projection lemma. -/
theorem view_weaken {α : Type} {first second : Sql α}
    {left : Sql.View first} {right : Sql.View second} {state : ExecutionContext}
    (same : left.EquivAt right state) : left.ObservationEquivAt right state := by
  apply (view_weak_profile_iff _ _ _).mpr
  exact observationProfile_transport ((view_full_profile_iff _ _ _).mp same)
    (Sql.Branch.actual first _ _ _) (Sql.Branch.actual second _ _ _)
    (fun one two _ _ equal => left.observation_eq_of_full right state one two equal)

/-- Equal weak view profiles become equal full profiles when matching branches also
agree on connection and raw step count. Proof sketch: generic transport adds exactly these
two frame facts through the full-observation characterization. -/
theorem view_strengthen {α : Type} {first second : Sql α}
    {left : Sql.View first} {right : Sql.View second} {state : ExecutionContext}
    (same : left.ObservationEquivAt right state)
    (connections : ∀ one two, first.Branch state.clock state.index state.connection one →
      second.Branch state.clock state.index state.connection two →
      left.observation one = right.observation two → one.connection = two.connection)
    (steps : ∀ one two, first.Branch state.clock state.index state.connection one →
      second.Branch state.clock state.index state.connection two →
      left.observation one = right.observation two → one.outputs.length = two.outputs.length) :
    left.EquivAt right state := by
  apply (view_full_profile_iff _ _ _).mpr
  exact observationProfile_transport ((view_weak_profile_iff _ _ _).mp same)
    (Sql.Branch.actual first _ _ _) (Sql.Branch.actual second _ _ _)
    (fun one two before after equal => (Sql.View.fullObservation_eq_iff _ _ _ _ _).mpr
      ⟨equal, connections one two before after equal, steps one two before after equal⟩)

/-- Full projected comparisons compose by ordinary equality transitivity.
Proof sketch: convert each comparison to its profile equality and compose them. -/
theorem view_trans {α : Type} {first second third : Sql α}
    {left : Sql.View first} {middle : Sql.View second} {right : Sql.View third} {state : ExecutionContext}
    (one : left.EquivAt middle state) (two : middle.EquivAt right state) : left.EquivAt right state :=
  (view_full_profile_iff _ _ _).mpr
    (((view_full_profile_iff _ _ _).mp one).trans ((view_full_profile_iff _ _ _).mp two))

/-- Two single-branch programs compare under any observer when their actual observations
agree. The observer can be either full or weak. Proof sketch: use the generic singleton law. -/
theorem sql_singleton_profiles {α Observation : Type} {first second : Sql α} {state : ExecutionContext}
    (left : SqlRun α → Observation) (right : SqlRun α → Observation)
    (leftOne : first.hasOneBranch state.clock state.index state.connection = true)
    (rightOne : second.hasOneBranch state.clock state.index state.connection = true)
    (same : left (first.runFrom state.clock state.index state.connection) =
      right (second.runFrom state.clock state.index state.connection)) :
    sqlProfile first state left = sqlProfile second state right :=
  observationProfile_of_singletons _ _ _ _ left right
    (fun result => Sql.branch_iff_actual first _ _ _ result leftOne)
    (fun result => Sql.branch_iff_actual second _ _ _ result rightOne) same

#print axioms full_profile_iff
#print axioms weak_profile_iff
#print axioms view_full_profile_iff
#print axioms view_weak_profile_iff
#print axioms view_weaken
#print axioms view_strengthen
#print axioms view_trans
#print axioms sql_singleton_profiles
end ProofBoundaries
