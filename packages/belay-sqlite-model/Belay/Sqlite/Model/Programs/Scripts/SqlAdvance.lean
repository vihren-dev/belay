import Belay.Sqlite.Model.Programs.Scripts.StatementStep
import Belay.Sqlite.Model.Programs.Scripts.SqlCounted
import Belay.Sqlite.Model.Schema.Dispatch.SqlAdvance

set_option doc.verso true

/-! The steps of script-directed SQL execution of resolved statements. Each statement runs
at the clock value that the state's clock assignment gives for its position;
{lit}`SqlExecution.lean` chooses the assignment. BEGIN records the
committed snapshot; an explicit COMMIT/ROLLBACK, or an INSERT that fails with the
ROLLBACK algorithm, changes transaction state. Other statement errors stop execution
without inferring connection closure, framework cleanup, or transaction rollback. A statement
that continues also gives the counters of the connection their new values (ADR 0024). -/
namespace Belay.Sqlite.Model

/-- For every position, statement, values, state and next state: if {name}`advance` continues
with the next state, then {name}`advanceWith` of the effect ({name}`literalStep`) continues with a
state, and the next state is that state with the counters after the counts of the run. Proof
sketch: {name}`SqlTransition.counted_eq_next`. -/
theorem advance_eq_next {position : Nat} {statement : Resolved.Statement} {parameters : List Value} {state next : SqlState}
    (continued : advance position statement parameters state = .next next) :
    ∃ transitioned, advanceWith position statement state
        ((SqlState.statementRun state (state.clock position) parameters statement).effect) = .next transitioned ∧
      next = { transitioned with
        counters := transitioned.counters.apply (SqlState.statementRun state (state.clock position) parameters statement).counts } :=
  SqlTransition.counted_eq_next.mp continued

/-- For every position, statement, values, state and outcome: if {name}`advance` halts with the
outcome, then {name}`advanceWith` of the effect ({name}`literalStep`) halts with it. Proof sketch:
{name}`SqlTransition.counted_eq_halt`. -/
theorem advance_eq_halt {position : Nat} {statement : Resolved.Statement} {parameters : List Value} {state : SqlState}
    {outcome : Outcome} (halted : advance position statement parameters state = .halt outcome) :
    advanceWith position statement state ((SqlState.statementRun state (state.clock position) parameters statement).effect) =
      .halt outcome :=
  SqlTransition.counted_eq_halt.mp halted

/-- Check {name}`statementReady` at every reached statement and follow the actual
transition, both from one run of the statement ({name}`runStatement`). After a halt,
unreachable statements impose no obligation. An empty script passes. -/
def supportedSqlFrom (position : Nat) (script : List (Resolved.Statement × List Value)) (state : SqlState) : Bool :=
  match script with
  | [] => true
  | (statement, parameters) :: rest =>
    let run := SqlState.statementRun state (state.clock position) parameters statement
    run.ready &&
    match advanceRun position statement state run with
    | .halt _ => true
    | .next next => supportedSqlFrom (position + 1) rest next

end Belay.Sqlite.Model
