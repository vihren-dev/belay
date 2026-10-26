import Belay.Sqlite.Model.RunHoldsReady
import Belay.Sqlite.Model.ScriptRunHolds
import Belay.Sqlite.Model.ScriptRunSingleton

set_option doc.verso true

/-! The run theorem for {lit}`runScriptFrom`, the run of the surface, for a statement theorem with the
support check and a condition that the invariant of the run gives (ADR 0022, D3, slice 4). A statement
that {lit}`runScriptFrom` runs has passed the support check, because the run ends at a statement that
fails it. The condition of a statement is not a hypothesis on the statements of the script: the theorem
asks that the invariant of the run, with the resolver, gives it for every connection that satisfies the
invariant. The theorems of the atoms prove that with the facts of the resolver. -/

namespace Belay.Sqlite.Model

variable {property : Database → Prop} {condition : Resolved.Statement → Database → Prop}

/-- For every property, condition, context, clock, index, connection, statement and list of values: if the
statement theorem with the support check holds ({name}`StatementKeepsReady`), the state of the connection
satisfies {name}`SqlState.Holds`, each statement that {name}`resolveStatement` gives for the statement meets the
condition on the database of the connection, and {name}`runScriptStep` continues with a next connection,
then the state of the next connection satisfies {name}`SqlState.Holds`. Proof sketch: as
{name}`runScriptStep_holds`; a step that continues has passed the support check. -/
theorem runScriptStep_holds_ready (keeps : StatementKeepsReady property condition) (context : ResolveContext)
    (clock : Option Clock) (index : Nat) {connection : Connection} (holds : connection.state.Holds property)
    (statement : Syntax.Statement) (parameters : List Value)
    (met : ∀ resolved after, resolveStatement context connection.resolveState statement = .ok (resolved, after) →
      condition resolved connection.state.database)
    {output : Output} {next : Connection} {others : List StatementExecution}
    (continued : runScriptStep context clock index connection statement parameters = .continued output next others) :
    next.state.Holds property := by
  obtain ⟨_, resolved, after, value, resolution, _, _, ready, _, _, rfl⟩ := runScriptStep_continued_spec continued
  exact Connection.afterStep_holds connection _ _ (SqlTransition.counted_holds _ (advanceWith_holds index resolved holds
    (keeps value _ parameters resolved _ holds.1 (met resolved after resolution) (Bool.and_eq_true_iff.mp ready).1)))

/-- The run theorem of {name}`runScriptFrom`, for a statement theorem with the support check and a condition
that the invariant gives. For every context and clock: if the statement theorem holds
({name}`StatementKeepsReady`), and for every connection that satisfies {name}`SqlState.Holds`, every statement
and every resolution of it over the connection ({name}`resolveStatement`), the resolved statement meets the
condition on the database of the connection, then for every index, connection and statements with their values:
if the state of the connection satisfies {name}`SqlState.Holds`, the state of the connection of the run
({lit}`connection.state`) satisfies it. Proof sketch: induction on the statements with
{name}`runScriptStep_holds_ready`; a run that ends keeps the connection. -/
theorem runScriptFrom_holds_derived (keeps : StatementKeepsReady property condition) (context : ResolveContext)
    (clock : Option Clock)
    (derive : ∀ (connection : Connection) (statement : Syntax.Statement) resolved after,
      connection.state.Holds property → resolveStatement context connection.resolveState statement = .ok (resolved, after) →
        condition resolved connection.state.database) :
    ∀ (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value)),
      connection.state.Holds property →
        (runScriptFrom context clock index connection script).connection.state.Holds property
  | _, _, [], holds => holds
  | index, connection, (statement, parameters) :: rest, holds => by
    unfold runScriptFrom
    cases step : runScriptStep context clock index connection statement parameters with
    | ended _ => exact holds
    | continued output next others =>
      obtain rfl := runScriptStep_others step
      have kept := runScriptStep_holds_ready keeps context clock index holds statement parameters
        (fun resolved after found => derive connection statement resolved after holds found) step
      exact runScriptFrom_holds_derived keeps context clock derive (index + 1) rest kept

/-- The run theorem of {name}`runScriptAllFrom`, for a statement theorem with the support check and a
condition that the invariant gives. For the hypotheses of {name}`runScriptFrom_holds_derived`: for every
index, connection and statements with their values, if the state of the connection satisfies
{name}`SqlState.Holds`, the state of the connection of every complete execution of the script satisfies
it. Proof sketch: {name}`runScriptFrom_holds_derived` holds for the traversal
({name}`runScriptAllFrom_forall`). -/
theorem runScriptAllFrom_holds_derived (keeps : StatementKeepsReady property condition) (context : ResolveContext)
    (clock : Option Clock)
    (derive : ∀ (connection : Connection) (statement : Syntax.Statement) resolved after,
      connection.state.Holds property → resolveStatement context connection.resolveState statement = .ok (resolved, after) →
        condition resolved connection.state.database)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds property) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds property :=
  runScriptAllFrom_forall context clock index connection script
    (runScriptFrom_holds_derived keeps context clock derive index script holds)

end Belay.Sqlite.Model
