import Belay.Sqlite.Model.KeysUniqueRunStep

set_option doc.verso true

/-! The run theorem of the atom "keys unique" for {lit}`runSqlFrom` and {lit}`runSql`
(ADR 0022, D3, slice 2): a run from a state whose database and snapshot keep the keys unique
gives an outcome whose databases keep them, when each statement that the run reaches meets its
condition. The hypothesis is necessary: finding 1 of the keys-unique status file
({lit}`KeysUniqueExamples.lean`) is a run of resolved statements without it whose outcome
breaks the atom. -/

namespace Belay.Sqlite.Model

/-- For the given position, script and state, each statement that {name}`runSqlFrom` reaches
meets its run condition ({name}`Resolved.Statement.RunCondition`) on the database of the state
before it:

* the empty script requires nothing;
* a script with a first statement requires the condition of that statement on the database of
  the state, and, when {name}`advance` of the statement continues with a next state, the
  conditions of the rest of the script from the next position and the next state. A halt
  requires nothing of the rest. -/
def RunConditions (position : Nat) : List (Resolved.Statement × List Value) → SqlState → Prop
  | [], _ => True
  | (statement, parameters) :: rest, state =>
    statement.RunCondition state.database ∧
      match advance position statement parameters state with
      | .halt _ => True
      | .next next => RunConditions (position + 1) rest next

/-- For every position, script and state: if each statement of the script has no run condition
({name}`Resolved.Statement.unconditioned`), the script meets {name}`RunConditions` from the
position and the state. Proof sketch: induction on the script with
{name}`Resolved.Statement.runCondition_of_unconditioned`. -/
theorem RunConditions.of_unconditioned :
    ∀ (position : Nat) (script : List (Resolved.Statement × List Value)) (state : SqlState),
      (script.all fun item => item.1.unconditioned) = true → RunConditions position script state
  | _, [], _, _ => trivial
  | position, (statement, parameters) :: rest, state, all => by
    simp only [List.all_cons, Bool.and_eq_true] at all
    refine ⟨Resolved.Statement.runCondition_of_unconditioned all.1, ?_⟩
    cases advance position statement parameters state with
    | halt _ => trivial
    | next next => exact RunConditions.of_unconditioned (position + 1) rest next all.2

/-- For every position, statement, list of values and state: if the state satisfies
{name}`SqlState.KeysUnique` and the statement meets its run condition on the database of the
state, the transition of {name}`advance` satisfies {name}`SqlTransition.KeysUnique`. Proof
sketch: {name}`advanceWith_keysUnique` of the effect of the statement theorem
{name}`runStatement_keysUnique`. -/
theorem advance_keysUnique (position : Nat) (statement : Resolved.Statement) (parameters : List Value)
    {state : SqlState} (unique : state.KeysUnique) (condition : statement.RunCondition state.database) :
    (advance position statement parameters state).KeysUnique :=
  advanceWith_keysUnique position statement unique
    (runStatement_keysUnique _ parameters statement unique.1
      (Resolved.Statement.keysCondition_of_runCondition condition))

/-- The run theorem of {name}`runSqlFrom`. For every position, script and state: if the state
satisfies {name}`SqlState.KeysUnique` (its database, and its snapshot when a transaction is
open) and the script meets {name}`RunConditions` from the position and the state, the outcome
of {name}`runSqlFrom` satisfies {name}`Outcome.KeysUnique`: the database of a success or a
failure, and the persisted and the visible database of a pending outcome. Proof sketch:
induction on the script with {name}`advance_keysUnique`; the end of the script is
{name}`SqlState.finish_keysUnique`. -/
theorem runSqlFrom_keysUnique :
    ∀ (position : Nat) (script : List (Resolved.Statement × List Value)) {state : SqlState},
      state.KeysUnique → RunConditions position script state → (runSqlFrom position script state).KeysUnique
  | _, [], _, unique, _ => SqlState.finish_keysUnique unique unique.1
  | position, (statement, parameters) :: rest, state, unique, conditions => by
    have step := advance_keysUnique position statement parameters unique conditions.1
    have later := conditions.2
    unfold runSqlFrom
    revert step later
    cases advance position statement parameters state with
    | halt outcome => exact fun step _ => step
    | next next => exact fun step later => runSqlFrom_keysUnique (position + 1) rest step later

/-- The run theorem of {name}`runSql`, the run that ADR 0022, D3 names. For every script and
database: if the database satisfies {name}`Database.KeysUnique` and the script meets
{name}`RunConditions` from position 0 and the state of the database outside a transaction, the
outcome of {name}`runSql` satisfies {name}`Outcome.KeysUnique`. Proof sketch:
{name}`runSqlFrom_keysUnique` from a state without a snapshot. -/
theorem runSql_keysUnique (script : List (Resolved.Statement × List Value)) {database : Database}
    (unique : database.KeysUnique) (conditions : RunConditions 0 script { database }) :
    (runSql script database).KeysUnique :=
  runSqlFrom_keysUnique 0 script ⟨unique, fun _ same => nomatch same⟩ conditions

end Belay.Sqlite.Model
