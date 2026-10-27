import Belay.Sqlite.Model.RunHolds
import Belay.Sqlite.Model.ScriptConditions
import Belay.Sqlite.Model.ScriptRunSingleton

set_option doc.verso true

/-! The run theorem for {lit}`runScriptFrom`, the run of the surface, for every property of
databases (ADR 0022, D3, slices 2 and 3): the connection at the end of the run has the property in
its database and its snapshot, when the statement theorem of the property holds and each statement
that the run resolves meets its condition. Slice 4 proves the resolver facts that give the
conditions and removes the hypothesis from the theorems of the atoms. -/

namespace Belay.Sqlite.Model

variable {property : Database → Prop} {condition : Resolved.Statement → Database → Prop}

/-- For every property, connection, resolution state, counts and transition: if the transition satisfies
{name}`SqlTransition.Holds`, the state of the connection after the transition
({name}`Connection.afterStep`) satisfies {name}`SqlState.Holds`. Proof sketch: a transition that
continues gives its state; a success or a failure leaves the connection without a snapshot; a
pending outcome keeps its persisted database as the snapshot. -/
theorem Connection.afterStep_holds (connection : Connection) (after : ResolveState) (counts : Counts) :
    ∀ {transition : SqlTransition}, transition.Holds property →
      (connection.afterStep after counts transition).state.Holds property
  | .next _, holds => holds
  | .halt (.success _), holds | .halt (.failure ..), holds => ⟨holds, fun _ same => nomatch same⟩
  | .halt (.pending ..), holds => ⟨holds.2, fun _ same => Option.some.inj same ▸ holds.1⟩

/-- For every property, condition, context, clock, index, connection, statement and list of values:
if the statement theorem holds ({name}`StatementKeeps`), the state of the connection satisfies
{name}`SqlState.Holds`, each statement that {name}`resolveStatement` gives for the statement meets
the condition on the database of the connection, and {name}`runScriptStep` continues, then the state
of the next connection of every execution of the step ({name}`RunStep.executions`) satisfies
{name}`SqlState.Holds`. Proof sketch: the next connection of an execution is the connection after the
transition of a run whose effect is the effect of an admitted execution of the statement
({name}`runScriptStep_execution_runs`); the statement theorem gives that effect the property
({name}`advanceWith_holds`, {name}`SqlTransition.counted_holds`), then {name}`Connection.afterStep_holds`. -/
theorem runScriptStep_holds (keeps : StatementKeeps property condition) (context : ResolveContext)
    (clock : Option Clock) (index : Nat) {connection : Connection} (holds : connection.state.Holds property)
    (statement : Syntax.Statement) (parameters : List Value)
    (met : ∀ resolved after, resolveStatement context connection.resolveState statement = .ok (resolved, after) →
      condition resolved connection.state.database)
    {output : Output} {next : Connection} {others : List StatementExecution}
    (continued : runScriptStep context clock index connection statement parameters = .continued output next others) :
    ∀ execution ∈ (RunStep.continued output next others).executions, execution.next.state.Holds property := by
  obtain ⟨resolved, after, value, resolution, _, runs⟩ := runScriptStep_execution_runs continued
  intro execution member
  obtain ⟨run, effectMember, same⟩ := runs execution member
  rw [same]
  exact Connection.afterStep_holds connection _ _ (SqlTransition.counted_holds _ (advanceWith_holds index resolved holds
    (keeps value (connection.state.counters.view resolved.counterReads) parameters resolved connection.state.database
      holds.1 (met resolved after resolution) run.effect effectMember)))

/-- The run theorem of {name}`runScriptFrom`, for every property and condition. For every context,
clock, index, connection and statements with their values: if the statement theorem holds
({name}`StatementKeeps`), the state of the connection satisfies {name}`SqlState.Holds` (its
database, and its snapshot when a transaction is open) and the statements meet
{name}`ScriptConditionsWith` from the index and the connection, the state of the connection of the
run ({lit}`connection.state`) satisfies {name}`SqlState.Holds`. Proof sketch: induction on the
statements with {name}`runScriptStep_holds` for the model's own execution; a run that ends keeps the connection. -/
theorem runScriptFrom_holds (keeps : StatementKeeps property condition) (context : ResolveContext)
    (clock : Option Clock) :
    ∀ (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value)),
      connection.state.Holds property → ScriptConditionsWith condition context clock index connection script →
        (runScriptFrom context clock index connection script).connection.state.Holds property
  | _, _, [], holds, _ => holds
  | index, connection, (statement, parameters) :: rest, holds, conditions => by
    unfold runScriptFrom
    cases step : runScriptStep context clock index connection statement parameters with
    | ended _ => exact holds
    | continued output next others =>
      have kept := runScriptStep_holds keeps context clock index holds statement parameters conditions.1 step
        { output, next } (by simp [RunStep.executions])
      have later := conditions.2
      rw [step] at later
      exact runScriptFrom_holds keeps context clock (index + 1) rest kept (later ⟨output, next⟩ (by simp [RunStep.executions]))

/-- The run theorem of {name}`runScriptAllFrom`, for every property and condition. For every context,
clock, index, connection and statements with their values: if the statement theorem holds
({name}`StatementKeeps`), the state of the connection satisfies {name}`SqlState.Holds` and the
statements meet {name}`ScriptConditionsWith`, then the state of the connection of every complete
execution of the script satisfies {name}`SqlState.Holds`. Proof sketch: induction on the statements;
{name}`runScriptStep_holds` gives the property for the connection of every execution of the first
statement, and a complete execution of the rest starts from one of them. -/
theorem runScriptAllFrom_holds (keeps : StatementKeeps property condition) (context : ResolveContext)
    (clock : Option Clock) :
    ∀ (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value)),
      connection.state.Holds property → ScriptConditionsWith condition context clock index connection script →
        ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds property
  | _, _, [], holds, _ => by
    intro run member
    simp only [runScriptAllFrom, runScriptAllWith, List.mem_singleton] at member
    subst member
    exact holds
  | index, connection, (statement, parameters) :: rest, holds, conditions => by
    intro run member
    unfold runScriptAllFrom at member
    cases step : runScriptStep context clock index connection statement parameters with
    | ended _ =>
      simp only [runScriptAllWith, step, List.mem_singleton] at member
      subst member
      exact holds
    | continued output next others =>
      simp only [runScriptAllWith, step, List.mem_flatMap, List.mem_map] at member
      obtain ⟨execution, inExecutions, later, inLater, rfl⟩ := member
      have kept := runScriptStep_holds keeps context clock index holds statement parameters conditions.1 step
        execution inExecutions
      have more := conditions.2
      rw [step] at more
      exact runScriptAllFrom_holds keeps context clock (index + 1) rest kept (more execution inExecutions) later inLater

end Belay.Sqlite.Model
