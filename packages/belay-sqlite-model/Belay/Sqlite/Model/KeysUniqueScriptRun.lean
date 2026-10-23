import Belay.Sqlite.Model.KeysUniqueRuns
import Belay.Sqlite.Model.ScriptRun

set_option doc.verso true

/-! The run theorem of the atom "keys unique" for {lit}`runScriptFrom`, the run of the surface
(ADR 0022, D3, slice 2): the connection at the end of the run keeps the keys unique in its
database and its snapshot, when each statement that the run resolves meets its condition. Slice
4 proves the resolver facts that give the condition and removes the hypothesis from this
theorem. -/

namespace Belay.Sqlite.Model

/-- For the given context, clock, index, connection and statements with their values, each
statement that {name}`runScriptFrom` resolves meets its run condition
({name}`Resolved.Statement.RunCondition`) on the database of the connection before it:

* the empty list requires nothing;
* a list with a first statement requires, for each resolved statement and state that
  {name}`resolveStatement` gives for the first statement over the connection, the condition of
  the resolved statement on the database of the connection; and, when
  {name}`runScriptStep` continues with a next connection, the conditions of the rest from the
  next index and the next connection. A statement at which the run ends requires nothing of the
  rest, and a statement that does not resolve requires no condition. -/
def ScriptConditions (context : ResolveContext) (clock : Option Clock) (index : Nat) (connection : Connection) :
    List (Syntax.Statement × List Value) → Prop
  | [] => True
  | (statement, parameters) :: rest =>
    (∀ resolved after, resolveStatement context connection.resolveState statement = .ok (resolved, after) →
      resolved.RunCondition connection.state.database) ∧
      match runScriptStep context clock index connection statement parameters with
      | .ended _ => True
      | .continued _ next => ScriptConditions context clock (index + 1) next rest

/-- For every connection, resolution state and transition: if the state of the connection satisfies
{name}`SqlState.KeysUnique` and the transition satisfies {name}`SqlTransition.KeysUnique`, the
state of the connection after the transition ({name}`Connection.afterStep`) satisfies
{name}`SqlState.KeysUnique`. Proof sketch: a transition that continues gives its state; a
success or a failure leaves the connection without a snapshot; a pending outcome keeps its
persisted database as the snapshot. -/
theorem Connection.afterStep_keysUnique (connection : Connection) (after : ResolveState) :
    ∀ {transition : SqlTransition}, transition.KeysUnique →
      (connection.afterStep after transition).state.KeysUnique
  | .next _, unique => unique
  | .halt (.success _), unique | .halt (.failure ..), unique => ⟨unique, fun _ same => nomatch same⟩
  | .halt (.pending ..), unique => ⟨unique.2, fun _ same => Option.some.inj same ▸ unique.1⟩

/-- For every context, clock, index, connection, statement and list of values: if the state of
the connection satisfies {name}`SqlState.KeysUnique`, each statement that
{name}`resolveStatement` gives for the statement meets its run condition on the database of
the connection, and {name}`runScriptStep` continues with a next connection, then the state of
the next connection satisfies {name}`SqlState.KeysUnique`. Proof sketch: the step runs the
resolved statement and advances with its effect ({name}`advanceWith_keysUnique` of
{name}`runStatement_keysUnique`), then {name}`Connection.afterStep_keysUnique`. -/
theorem runScriptStep_keysUnique (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (unique : connection.state.KeysUnique) (statement : Syntax.Statement)
    (parameters : List Value)
    (condition : ∀ resolved after, resolveStatement context connection.resolveState statement = .ok (resolved, after) →
      resolved.RunCondition connection.state.database)
    {output : Output} {next : Connection}
    (continued : runScriptStep context clock index connection statement parameters = .continued output next) :
    next.state.KeysUnique := by
  unfold runScriptStep runScriptStepWith ranScriptStep at continued
  split at continued
  · nomatch continued
  · rename_i resolved after resolvedEq
    split at continued
    · nomatch continued
    · rename_i value _
      dsimp only at continued
      split at continued
      · nomatch continued
      · split at continued
        · nomatch continued
        all_goals
          injection continued with _ same
          subst same
          exact Connection.afterStep_keysUnique connection _ (advanceWith_keysUnique index resolved unique
            (runStatement_keysUnique value parameters resolved unique.1
              (Resolved.Statement.keysCondition_of_runCondition (condition resolved after resolvedEq))))

/-- The run theorem of {name}`runScriptFrom`. For every context, clock, index, connection and
statements with their values: if the state of the connection satisfies
{name}`SqlState.KeysUnique` (its database, and its snapshot when a transaction is open) and the
statements meet {name}`ScriptConditions` from the index and the connection, the state of the
connection of the run ({lit}`connection.state`) satisfies {name}`SqlState.KeysUnique`. Proof
sketch: induction on the statements with {name}`runScriptStep_keysUnique`; a run that ends keeps
the connection. -/
theorem runScriptFrom_keysUnique (context : ResolveContext) (clock : Option Clock) :
    ∀ (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value)),
      connection.state.KeysUnique → ScriptConditions context clock index connection script →
        (runScriptFrom context clock index connection script).connection.state.KeysUnique
  | _, _, [], unique, _ => unique
  | index, connection, (statement, parameters) :: rest, unique, conditions => by
    have step : ∀ output next, runScriptStep context clock index connection statement parameters = .continued output next →
        next.state.KeysUnique := fun _ _ =>
      runScriptStep_keysUnique context clock index unique statement parameters conditions.1
    have later := conditions.2
    unfold runScriptFrom
    revert step later
    cases runScriptStep context clock index connection statement parameters with
    | ended _ => exact fun _ _ => unique
    | continued output next =>
      exact fun step later => runScriptFrom_keysUnique context clock (index + 1) rest (step output next rfl) later

end Belay.Sqlite.Model
