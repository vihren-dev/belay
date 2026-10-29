import Belay.Sqlite.Model.RunHoldsReady

set_option doc.verso true

/-! An isolated experiment for one execution-input condition and one resolved
run preservation induction. The old-formula adapters test theorem strength;
they are experimental evidence, not proposed compatibility APIs. -/

namespace Belay.Sqlite.Model.ContextExperiment

/-- The condition can inspect every input of {name}`runStatement` used by ordinary
execution. For example, a condition can require its support check. Use a constant
true predicate when the property needs no condition. -/
abbrev Condition := Int → Counters → List Value → Resolved.Statement → Database → Prop

/-- For every clock, counters, parameters, statement and database, if the database
has the property and the condition holds on those inputs, the effect has the
property on success and partial constraint failure. Other errors require nothing
of the effect database. -/
def Keeps (property : Database → Prop) (condition : Condition) : Prop :=
  ∀ clock counters parameters statement database,
    property database → condition clock counters parameters statement database →
      (runStatement clock counters parameters statement database).effect.Satisfies property

/-- For the given position, script and state, each reached statement meets the
condition with its actual clock, visible counters, parameters and database. The
empty script and the suffix after a halt require nothing. -/
def Conditions (condition : Condition) (position : Nat) :
    List (Resolved.Statement × List Value) → SqlState → Prop
  | [], _ => True
  | (statement, parameters) :: rest, state =>
    condition (state.clock position) (state.counters.view statement.counterReads)
      parameters statement state.database ∧
      match advance position statement parameters state with
      | .halt _ => True
      | .next next => Conditions condition (position + 1) rest next

/-- For every property and execution condition, if a state and its snapshot have
the property, a preservation rule and the condition at this statement imply that
the transition preserves every database carried by its state or outcome.
Proof sketch: use the existing effect and counter transport lemmas. -/
theorem advance_keeps {property : Database → Prop} {condition : Condition}
    (keeps : Keeps property condition) (position : Nat) (statement : Resolved.Statement)
    (parameters : List Value) {state : SqlState} (holds : state.Holds property)
    (met : condition (state.clock position) (state.counters.view statement.counterReads)
      parameters statement state.database) :
    (advance position statement parameters state).Holds property :=
  SqlTransition.counted_holds _ (advanceWith_holds position statement holds
    (keeps _ _ parameters statement _ holds.1 met))

/-- For every property, execution condition, position, script and state, a
preservation rule, the property on the state and its snapshot, and the condition
at every reached statement imply the property on every outcome database.
Proof sketch: one induction on the script uses {name}`advance_keeps`; EOF uses
the existing finish theorem, which also retains an open transaction snapshot. -/
theorem run_keeps {property : Database → Prop} {condition : Condition}
    (keeps : Keeps property condition) :
    ∀ (position : Nat) (script : List (Resolved.Statement × List Value)) {state : SqlState},
      state.Holds property → Conditions condition position script state →
        (runSqlFrom position script state).Holds property
  | _, [], _, holds, _ => SqlState.finish_holds holds holds.1
  | position, (statement, parameters) :: rest, state, holds, conditions => by
    have step := advance_keeps keeps position statement parameters holds conditions.1
    have later := conditions.2
    unfold runSqlFrom
    revert step later
    cases advance position statement parameters state with
    | halt outcome => exact fun step _ => step
    | next next => exact fun step later => run_keeps keeps (position + 1) rest step later

/-- For every old statement condition and run, its reached-statement obligations
imply the contextual obligations that ignore the additional inputs.
Proof sketch: induction follows the same transition, including halted suffixes. -/
theorem conditions_plain {condition : Resolved.Statement → Database → Prop} :
    ∀ position script state, RunConditionsWith condition position script state →
      Conditions (fun _ _ _ => condition) position script state
  | _, [], _, _ => trivial
  | position, (statement, parameters) :: rest, state, met => by
    refine ⟨met.1, ?_⟩
    have later := met.2
    revert later
    cases advance position statement parameters state with
    | halt _ => exact fun _ => trivial
    | next next => exact conditions_plain (position + 1) rest next

/-- For every old statement condition and run, its reached-statement obligations
and the support check imply contextual obligations with raw statement readiness.
The state support check includes another counter check; this implication only
uses its raw readiness part. Proof sketch: induction follows the actual run. -/
theorem conditions_ready {condition : Resolved.Statement → Database → Prop} :
    ∀ position script state, RunConditionsWith condition position script state →
      supportedSqlFrom position script state = true →
      Conditions (fun clock counters parameters statement database =>
        condition statement database ∧
          (runStatement clock counters parameters statement database).ready = true)
        position script state
  | _, [], _, _, _ => trivial
  | position, (statement, parameters) :: rest, state, met, supported => by
    simp only [supportedSqlFrom, Bool.and_eq_true] at supported
    refine ⟨⟨met.1, (Bool.and_eq_true_iff.mp supported.1).1⟩, ?_⟩
    have later := met.2
    have laterReady := supported.2
    unfold advance
    unfold advance at later
    revert later laterReady
    cases advanceRun position statement state
      (SqlState.statementRun state (state.clock position) parameters statement) with
    | halt _ => exact fun _ _ => trivial
    | next next => exact conditions_ready (position + 1) rest next

/-- The old unconditional run formula follows with precisely its original
assumptions. It imposes no readiness premise. Proof sketch: instantiate the
contextual theorem with a condition that ignores the extra execution inputs. -/
theorem old_plain_formula {property : Database → Prop}
    {condition : Resolved.Statement → Database → Prop}
    (keeps : StatementKeeps property condition) (position : Nat)
    (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds property) (met : RunConditionsWith condition position script state) :
    (runSqlFrom position script state).Holds property :=
  run_keeps keeps position script holds (conditions_plain position script state met)

/-- The old support-dependent run formula follows with precisely its original
assumptions. Proof sketch: pair the old condition with raw readiness and apply
the same contextual run theorem as the unconditional formula. -/
theorem old_ready_formula {property : Database → Prop}
    {condition : Resolved.Statement → Database → Prop}
    (keeps : StatementKeepsReady property condition) (position : Nat)
    (script : List (Resolved.Statement × List Value)) {state : SqlState}
    (holds : state.Holds property) (supported : supportedSqlFrom position script state = true)
    (met : RunConditionsWith condition position script state) :
    (runSqlFrom position script state).Holds property :=
  run_keeps (fun clock counters parameters statement database holds met =>
    keeps clock counters parameters statement database holds met.1 met.2)
    position script holds (conditions_ready position script state met supported)

#print axioms run_keeps
#print axioms old_plain_formula
#print axioms old_ready_formula

end Belay.Sqlite.Model.ContextExperiment
