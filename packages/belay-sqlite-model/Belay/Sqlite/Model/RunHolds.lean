import Belay.Sqlite.Model.RunHoldsStep

set_option doc.verso true

/-! Preservation through resolved execution. One condition reads the actual evaluator inputs;
readiness, when needed, is part of that condition. One induction preserves every outcome database. -/

namespace Belay.Sqlite.Model

/-- A proposition about the clock, visible counters, parameters, statement and database passed to
{name}`runStatement`. A readiness condition can inspect all five inputs. Use
{lean}`fun (_ : Int) (_ : Counters) (_ : List Value) (_ : Resolved.Statement) (_ : Database) => True`
when a property needs no condition. -/
abbrev StatementCondition := Int → Counters → List Value → Resolved.Statement → Database → Prop

/-- For every clock, counters, parameters, statement and database: if the database has the property
and the condition holds on those inputs, every effect in {name}`StatementRun.effects` of
{name}`runStatement` satisfies the property. Success and partial constraint FAIL constrain the
returned database; every other error requires nothing of its effect database. -/
def StatementKeeps (property : Database → Prop) (condition : StatementCondition) : Prop :=
  ∀ clock counters parameters statement database,
    property database → condition clock counters parameters statement database →
      ∀ effect ∈ (runStatement clock counters parameters statement database).effects, effect.Satisfies property

/-- For the given condition, position, script and state, each reached statement meets the condition
with the actual clock, visible counters, parameters and database used by {name}`advance`.
The empty script and the suffix after a halt require nothing. -/
def RunConditionsWith (condition : StatementCondition) (position : Nat) :
    List (Resolved.Statement × List Value) → SqlState → Prop
  | [], _ => True
  | (statement, parameters) :: rest, state =>
    condition (state.clock position) (state.counters.view statement.counterReads) parameters statement state.database ∧
      match advance position statement parameters state with
      | .halt _ => True
      | .next next => RunConditionsWith condition (position + 1) rest next

/-- For every condition and statement test: if an accepted statement meets the condition for every
clock, counters, parameters and database, a script of accepted statements meets
{name}`RunConditionsWith` from every position and state. Proof sketch: follow each reached transition. -/
theorem RunConditionsWith.of_unconditioned {condition : StatementCondition}
    {unconditioned : Resolved.Statement → Bool}
    (free : ∀ clock counters parameters statement database,
      unconditioned statement = true → condition clock counters parameters statement database) :
    ∀ (position : Nat) (script : List (Resolved.Statement × List Value)) (state : SqlState),
      (script.all fun item => unconditioned item.1) = true → RunConditionsWith condition position script state
  | _, [], _, _ => trivial
  | position, (statement, parameters) :: rest, state, all => by
    simp only [List.all_cons, Bool.and_eq_true] at all
    refine ⟨free _ _ _ _ _ all.1, ?_⟩
    cases advance position statement parameters state with
    | halt _ => trivial
    | next next => exact RunConditionsWith.of_unconditioned free (position + 1) rest next all.2

variable {property : Database → Prop} {condition : StatementCondition}

/-- For every property, condition and resolved step: preservation evidence, the property on the
state and its snapshot, and the condition at the actual evaluator inputs imply the property on
every database carried by the transition. Proof sketch: apply {name}`advanceWith_holds` to the
canonical member of the effects, then transport the result through counter updates. -/
theorem advance_holds (keeps : StatementKeeps property condition) (position : Nat) (statement : Resolved.Statement)
    (parameters : List Value) {state : SqlState} (holds : state.Holds property)
    (met : condition (state.clock position) (state.counters.view statement.counterReads)
      parameters statement state.database) : (advance position statement parameters state).Holds property :=
  SqlTransition.counted_holds _ (advanceWith_holds position statement holds
    (keeps _ _ parameters statement _ holds.1 met _ (StatementRun.effect_mem_effects _)))

/-- For every property, condition, position, script and state: preservation evidence, the property
on the state and its snapshot, and conditions at every reached step imply the property on the
success/failure database and both persisted and visible databases of a pending outcome.
Proof sketch: one script induction applies {name}`advance_holds`; EOF uses {name}`SqlState.finish_holds`. -/
theorem runSqlFrom_holds (keeps : StatementKeeps property condition) :
    ∀ (position : Nat) (script : List (Resolved.Statement × List Value)) {state : SqlState},
      state.Holds property → RunConditionsWith condition position script state →
        (runSqlFrom position script state).Holds property
  | _, [], _, holds, _ => SqlState.finish_holds holds holds.1
  | position, (statement, parameters) :: rest, state, holds, conditions => by
    have step := advance_holds keeps position statement parameters holds conditions.1
    have later := conditions.2
    unfold runSqlFrom
    revert step later
    cases advance position statement parameters state with
    | halt outcome => exact fun step _ => step
    | next next => exact fun step later => runSqlFrom_holds keeps (position + 1) rest step later

/-- For every property, condition, script and database: preservation evidence, the property on the
database and the script's reached conditions imply the property on every outcome database.
Proof sketch: apply {name}`runSqlFrom_holds` at position zero without a transaction snapshot. -/
theorem runSql_holds (keeps : StatementKeeps property condition) (script : List (Resolved.Statement × List Value))
    {database : Database} (holds : property database) (conditions : RunConditionsWith condition 0 script { database }) :
    (runSql script database).Holds property :=
  runSqlFrom_holds keeps 0 script ⟨holds, fun _ same => nomatch same⟩ conditions

/-- For every two properties and conditions, preservation evidence for each gives evidence for their
conjunction, with both conditions on the same evaluator inputs. Proof sketch: every kept effect
database satisfies each property independently. -/
theorem StatementKeeps.and {other : Database → Prop} {otherCondition : StatementCondition}
    (first : StatementKeeps property condition) (second : StatementKeeps other otherCondition) :
    StatementKeeps (fun database => property database ∧ other database)
      (fun clock counters parameters statement database =>
        condition clock counters parameters statement database ∧ otherCondition clock counters parameters statement database) :=
  fun clock counters parameters statement database holds met effect member after kept =>
    ⟨first clock counters parameters statement database holds.1 met.1 effect member after kept,
      second clock counters parameters statement database holds.2 met.2 effect member after kept⟩

/-- For every two properties, an implication between them transports the property on a state and
its snapshot. Proof sketch: apply the implication separately to both databases. -/
theorem SqlState.Holds.mono {other : Database → Prop} {state : SqlState} (holds : state.Holds property)
    (implies : ∀ database, property database → other database) : state.Holds other :=
  ⟨implies _ holds.1, fun snapshot same => implies _ (holds.2 snapshot same)⟩

/-- Every script meets the true condition from every position and state.
Proof sketch: every statement passes the constant test in {name}`RunConditionsWith.of_unconditioned`. -/
theorem RunConditionsWith.always (position : Nat) (script : List (Resolved.Statement × List Value))
    (state : SqlState) : RunConditionsWith (fun _ _ _ _ _ => True) position script state :=
  RunConditionsWith.of_unconditioned (unconditioned := fun _ => true) (fun _ _ _ _ _ _ => trivial)
    position script state (by simp)

/-- For every condition, position, script and state: reached conditions and the supported-run check
imply those conditions together with raw statement readiness at the same actual inputs. The state
check also requires counter knowledge; only its raw-readiness implication is used here.
Proof sketch: follow the reached transitions and project each state's support check. -/
theorem RunConditionsWith.with_ready :
    ∀ (position : Nat) (script : List (Resolved.Statement × List Value)) (state : SqlState),
      RunConditionsWith condition position script state → supportedSqlFrom position script state = true →
      RunConditionsWith (fun clock counters parameters statement database =>
        condition clock counters parameters statement database ∧
          (runStatement clock counters parameters statement database).ready = true) position script state
  | _, [], _, _, _ => trivial
  | position, (statement, parameters) :: rest, state, met, supported => by
    simp only [supportedSqlFrom, Bool.and_eq_true] at supported
    refine ⟨⟨met.1, (Bool.and_eq_true_iff.mp supported.1).1⟩, ?_⟩
    have later := met.2
    have readyLater := supported.2
    unfold advance at later ⊢
    revert later readyLater
    cases advanceRun position statement state
      (SqlState.statementRun state (state.clock position) parameters statement) with
    | halt _ => exact fun _ _ => trivial
    | next next => exact RunConditionsWith.with_ready (position + 1) rest next

end Belay.Sqlite.Model
