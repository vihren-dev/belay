import Belay.Sqlite.Model

/-! Temporary witnesses freeze the generic predicates from 3e2212ed6983. These old predicates
are test-local and retire after final condition acceptance, together with the API witnesses. -/

namespace PreservationMigration
open Belay.Sqlite.Model

/-- The frozen old preservation contract ignores the extra inputs only in its condition. -/
def PlainKeeps (property : Database → Prop) (condition : Resolved.Statement → Database → Prop) : Prop :=
  ∀ clock counters parameters statement database, property database → condition statement database →
    ∀ effect ∈ (runStatement clock counters parameters statement database).effects, effect.Satisfies property

/-- The old ready contract puts raw readiness after the statement/database condition. -/
def ReadyKeeps (property : Database → Prop) (condition : Resolved.Statement → Database → Prop) : Prop :=
  ∀ clock counters parameters statement database, property database → condition statement database →
    (runStatement clock counters parameters statement database).ready = true →
    ∀ effect ∈ (runStatement clock counters parameters statement database).effects, effect.Satisfies property

/-- The frozen raw predicate checks the old condition before each actual transition and stops at a halt. -/
def RawConditions (condition : Resolved.Statement → Database → Prop) (position : Nat) :
    List (Resolved.Statement × List Value) → SqlState → Prop
  | [], _ => True
  | (statement, parameters) :: rest, state => condition statement state.database ∧
      match advance position statement parameters state with
      | .halt _ => True
      | .next next => RawConditions condition (position + 1) rest next

/-- The unchanged old obligation supplies the new actual-input condition that ignores extra inputs. -/
theorem raw_conditions {condition : Resolved.Statement → Database → Prop} :
    ∀ position script state, RawConditions condition position script state →
      RunConditionsWith (fun _ _ _ => condition) position script state
  | _, [], _, _ => trivial
  | position, (statement, parameters) :: rest, state, met => by
    refine ⟨met.1, ?_⟩
    have later := met.2
    revert later
    cases advance position statement parameters state with
    | halt _ => exact fun _ => trivial
    | next next => exact raw_conditions (position + 1) rest next

/-- The old true condition is satisfied by every script, regardless of support. -/
theorem raw_always (position : Nat) (script : List (Resolved.Statement × List Value)) (state : SqlState) :
    RawConditions (fun _ _ => True) position script state := by
  induction script generalizing position state with
  | nil => trivial
  | cons entry rest ih =>
    obtain ⟨statement, parameters⟩ := entry
    refine ⟨trivial, ?_⟩
    cases advance position statement parameters state with
    | halt _ => trivial
    | next next => exact ih (position + 1) next

/-- A current certificate implies the old ready evidence when its condition follows from the old one and readiness. -/
theorem under_ready {property : Database → Prop} {condition : StatementCondition}
    {old : Resolved.Statement → Database → Prop} (keeps : StatementKeeps property condition)
    (adapt : ∀ clock counters parameters statement database, old statement database →
      (runStatement clock counters parameters statement database).ready = true →
      condition clock counters parameters statement database) : ReadyKeeps property old :=
  fun clock counters parameters statement database holds met ready =>
    keeps clock counters parameters statement database holds (adapt _ _ _ _ _ met ready)

/-- The full old unconditional generic formula, with no readiness or supported-run premise. -/
theorem raw {property : Database → Prop} {condition : Resolved.Statement → Database → Prop}
    (keeps : PlainKeeps property condition) (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState} (holds : state.Holds property) (conditions : RawConditions condition position script state) :
    (runSqlFrom position script state).Holds property :=
  runSqlFrom_holds keeps position script holds (raw_conditions position script state conditions)

/-- The full old supported generic formula retains precisely the supported-run premise. -/
theorem raw_ready {property : Database → Prop} {condition : Resolved.Statement → Database → Prop}
    (keeps : ReadyKeeps property condition) (position : Nat) (script : List (Resolved.Statement × List Value))
    {state : SqlState} (holds : state.Holds property) (supported : supportedSqlFrom position script state = true)
    (conditions : RawConditions condition position script state) : (runSqlFrom position script state).Holds property :=
  runSqlFrom_holds (fun clock counters parameters statement database holds met =>
    keeps clock counters parameters statement database holds met.1 met.2) position script holds
    (RunConditionsWith.with_ready position script state
      (raw_conditions position script state conditions) supported)

/-- The old unconditional zero-position entry follows from the common raw proof. -/
theorem raw_zero {property : Database → Prop} {condition : Resolved.Statement → Database → Prop}
    (keeps : PlainKeeps property condition) (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : property database) (conditions : RawConditions condition 0 script { database }) :
    (runSql script database).Holds property :=
  raw keeps 0 script ⟨holds, fun _ same => nomatch same⟩ conditions

/-- The old supported zero-position entry follows with the same support and condition premises. -/
theorem raw_ready_zero {property : Database → Prop} {condition : Resolved.Statement → Database → Prop}
    (keeps : ReadyKeeps property condition) (script : List (Resolved.Statement × List Value)) {database : Database}
    (holds : property database) (supported : supportedSqlFrom 0 script { database } = true)
    (conditions : RawConditions condition 0 script { database }) : (runSql script database).Holds property :=
  raw_ready keeps 0 script ⟨holds, fun _ same => nomatch same⟩ supported conditions

end PreservationMigration
