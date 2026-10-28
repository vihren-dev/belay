import Belay.Sqlite.ExecutionViewEquivalence

set_option doc.verso true

namespace ExecutionProfileMigration
open Belay.Sqlite

/-! Temporary universal witnesses for the four relation formulas before the profile
refactor. Retire after the integrated Nix acceptance records this revision. -/

/-- Complete profiles retain actual-run equality and precisely the old branch relation. -/
theorem complete_formula {α : Type} (first second : Sql α) (state : ExecutionContext) :
    first.EquivAt second state ↔
      first.runFrom state.clock state.index state.connection =
        second.runFrom state.clock state.index state.connection ∧
      ∀ result, first.Branch state.clock state.index state.connection result ↔
        second.Branch state.clock state.index state.connection result :=
  observationProfile_id_eq_iff

/-- Weak profiles retain actual observations and the old existential branch observations. -/
theorem observation_formula {α : Type} (first second : Sql α) (state : ExecutionContext) :
    first.ObservationEquivAt second state ↔
      (first.runFrom state.clock state.index state.connection).observation =
        (second.runFrom state.clock state.index state.connection).observation ∧
      ∀ observation,
        (∃ result, first.Branch state.clock state.index state.connection result ∧
          result.observation = observation) ↔
        (∃ result, second.Branch state.clock state.index state.connection result ∧
          result.observation = observation) :=
  observationProfile_eq_iff

/-- Full view profiles retain connection, clock, raw index and projected trace. -/
theorem view_formula {α : Type} {first second : Sql α}
    (left : Sql.View first) (right : Sql.View second) (state : ExecutionContext) :
    left.EquivAt right state ↔
      left.fullObservation state (first.runFrom state.clock state.index state.connection) =
        right.fullObservation state (second.runFrom state.clock state.index state.connection) ∧
      ∀ observation,
        (∃ result, first.Branch state.clock state.index state.connection result ∧
          left.fullObservation state result = observation) ↔
        (∃ result, second.Branch state.clock state.index state.connection result ∧
          right.fullObservation state result = observation) :=
  observationProfile_eq_iff

/-- Weak view profiles retain optional values and projected traces for actual and all branches. -/
theorem view_observation_formula {α : Type} {first second : Sql α}
    (left : Sql.View first) (right : Sql.View second) (state : ExecutionContext) :
    left.ObservationEquivAt right state ↔
      left.observation (first.runFrom state.clock state.index state.connection) =
        right.observation (second.runFrom state.clock state.index state.connection) ∧
      ∀ observation,
        (∃ result, first.Branch state.clock state.index state.connection result ∧
          left.observation result = observation) ↔
        (∃ result, second.Branch state.clock state.index state.connection result ∧
          right.observation result = observation) :=
  observationProfile_eq_iff

#print axioms complete_formula
#print axioms observation_formula
#print axioms view_formula
#print axioms view_observation_formula
end ExecutionProfileMigration
