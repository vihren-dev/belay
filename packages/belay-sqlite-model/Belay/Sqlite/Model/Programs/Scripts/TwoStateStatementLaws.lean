import Belay.Sqlite.Model.Programs.Scripts.QueryStepOutput
import Belay.Sqlite.Model.Schema.Dispatch.TwoStateStatementLaws

set_option doc.verso true

/-! Source agreement ({lit}`SourceAgreement.lean`) lifted from the
query to the statement and to its output (ADR 0017, S6): the run, the results that SQLite may
give and the output of a resolved statement do not depend on the initial database when the statement
has no source in it. A statement that is not a query ignores the initial database. -/

namespace Belay.Sqlite.Model

/-- For every state, clock value, values, statement and two optional initial databases, a statement with no
source in the initial database has the same run on the state whichever initial database is given
({name}`SqlState.statementRun`). Proof sketch: the run is {name}`runStatement` on the database of the state, which is
the same by {name}`runStatement_initial_irrelevant`. -/
theorem SqlState.statementRun_initial_irrelevant (state : SqlState) (clock : Int) (parameters : List Value)
    (statement : Resolved.Statement) (first second : Option Database) (plain : statement.readsInitial = false) :
    SqlState.statementRun state clock parameters statement first = SqlState.statementRun state clock parameters statement second := by
  unfold SqlState.statementRun
  rw [runStatement_initial_irrelevant _ _ parameters statement _ first second plain]

/-- For every clock value, values, statement, state, transition and two optional initial databases, a
statement with no source in the initial database has the same results that SQLite may give whichever
initial database is given ({name}`possibleOutput`). Proof sketch: for a query with a transition that runs, the result
is {name}`Resolved.Query.possibleOn_initial_irrelevant`; the other cases of the statement and transition do not
mention the initial database. -/
theorem possibleOutput_initial_irrelevant (clock : Int) (parameters : List Value) (statement : Resolved.Statement)
    (before : SqlState) (transition : SqlTransition) (first second : Option Database)
    (plain : statement.readsInitial = false) :
    possibleOutput clock parameters statement before transition first =
      possibleOutput clock parameters statement before transition second := by
  cases statement
  case query query subqueries =>
    obtain ⟨own, nested⟩ := Resolved.Statement.readsInitial_query plain
    cases transition
    · simp only [possibleOutput]
      exact Resolved.Query.possibleOn_initial_irrelevant query clock _ parameters before.database subqueries first second
        own nested
    · rfl
  all_goals rfl

/-- For every clock value, values, statement, state, run, transition and two optional initial databases, a
statement with no source in the initial database has the same output whichever initial database is given
({name}`Output.ofStep`). Proof sketch: the output is built from {name}`possibleOutput`, which is the same by
{name}`possibleOutput_initial_irrelevant`. -/
theorem Output.ofStep_initial_irrelevant (clock : Int) (parameters : List Value) (statement : Resolved.Statement)
    (before : SqlState) (run : StatementRun) (transition : SqlTransition) (first second : Option Database)
    (plain : statement.readsInitial = false) :
    Output.ofStep clock parameters statement before run transition first =
      Output.ofStep clock parameters statement before run transition second := by
  unfold Output.ofStep
  rw [possibleOutput_initial_irrelevant clock parameters statement before transition first second plain]

/-- For every clock, index, connection, values, resolved statement and two optional initial databases, a
statement with no source in the initial database has the same output whichever initial database is given
({name}`resolvedStepOutput`). In plain words: the output of a statement that does not read the initial origin
is independent of the initial database that is supplied, and the same as with none. Proof sketch: the
run and the output depend on the initial database only through the laws above. -/
theorem resolvedStepOutput_initial_irrelevant (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) (resolved : Resolved.Statement) (first second : Option Database)
    (plain : resolved.readsInitial = false) :
    resolvedStepOutput clock index connection parameters resolved first =
      resolvedStepOutput clock index connection parameters resolved second := by
  unfold resolvedStepOutput
  cases statementClock clock index resolved with
  | none => rfl
  | some value =>
    simp only []
    cases connection.state.counters.firstUnknown resolved.counterReads with
    | some kind => rfl
    | none =>
      simp only []
      rw [SqlState.statementRun_initial_irrelevant _ _ _ _ first second plain,
        Output.ofStep_initial_irrelevant _ _ _ _ _ _ first second plain]

end Belay.Sqlite.Model
