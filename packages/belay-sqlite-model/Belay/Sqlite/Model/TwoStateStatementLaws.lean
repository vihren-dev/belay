import Belay.Sqlite.Model.TwoStateCurrentLaws
import Belay.Sqlite.Model.QueryStepOutput

set_option doc.verso true

/-! The laws of {lit}`TwoStateReads.lean` and {lit}`TwoStateCurrentLaws.lean` lifted from the
query to the statement and to its output (ADR 0017, S6): the run, the results that SQLite may
give and the output of a resolved statement do not depend on the initial database when the statement
has no source in it. A statement that is not a query ignores the initial database. -/

namespace Belay.Sqlite.Model

/-- Whether a resolved statement reads the initial database: it is a query, or has a subquery, with a
source in it ({name}`Resolved.Query.readsInitial`). A statement that is not a query reads no
initial database, because the resolver gives sources of the initial origin only to queries. -/
def Resolved.Statement.readsInitial : Resolved.Statement → Bool
  | .query main inner => main.readsInitial || inner.any Resolved.Query.readsInitial
  | .createView .. | .createTable .. | .createIndex .. | .createTrigger .. | .addColumn .. | .rewrite _ | .drop ..
  | .begin | .commit | .rollback | .insert .. | .update .. | .upsert .. | .insertSelect .. | .delete .. | .prepareError _
  | .setting .. => false

/-- For every query and subqueries, if the statement {lit}`query subqueries` reads no initial database, then
neither does the query and neither does any subquery. Proof sketch: unfold {name}`Resolved.Statement.readsInitial`;
a disjunction that is false has two false sides, and a failed {lit}`any` has a false test for each member. -/
theorem Resolved.Statement.readsInitial_query {query : Resolved.Query} {subqueries : List Resolved.Query}
    (plain : (Resolved.Statement.query query subqueries).readsInitial = false) :
    query.readsInitial = false ∧ ∀ other ∈ subqueries, other.readsInitial = false := by
  simp only [Resolved.Statement.readsInitial, Bool.or_eq_false_iff, List.any_eq_false] at plain
  exact ⟨plain.1, fun other found => by simpa using plain.2 other found⟩

/-- For every query, clock value, counters, values, database, subqueries and two optional initial
databases, a query and subqueries with no source in the initial database run the same whichever
initial database is given ({name}`Resolved.Query.runOn`). Proof sketch: rewrite the statement's context
and the source rows with the laws of {lit}`TwoStateReads.lean`. -/
theorem Resolved.Query.runOn_initial_irrelevant (query : Resolved.Query) (clock : Int) (counters : Counters)
    (parameters : List Value) (database : Database) (subqueries : List Resolved.Query) (first second : Option Database)
    (own : query.readsInitial = false) (nested : ∀ other ∈ subqueries, other.readsInitial = false) :
    query.runOn clock counters parameters database subqueries first =
      query.runOn clock counters parameters database subqueries second := by
  unfold Resolved.Query.runOn
  simp only [Resolved.statementContext_initial_irrelevant clock counters parameters database subqueries first second nested,
    Resolved.Query.source_initial_irrelevant (query := query) (database := database) (first := first)
      (second := second) (own := own)]

/-- As {name}`Resolved.Query.runOn_initial_irrelevant`, for the results that SQLite may give
({name}`Resolved.Query.possibleOn`). Proof sketch: the context of the statement and the source rows are the same
by the laws of {lit}`TwoStateReads.lean`, and the rest of the result does not mention the initial database. -/
theorem Resolved.Query.possibleOn_initial_irrelevant (query : Resolved.Query) (clock : Int) (counters : Counters)
    (parameters : List Value) (database : Database) (subqueries : List Resolved.Query) (first second : Option Database)
    (own : query.readsInitial = false) (nested : ∀ other ∈ subqueries, other.readsInitial = false) :
    query.possibleOn clock counters parameters database subqueries first =
      query.possibleOn clock counters parameters database subqueries second := by
  unfold Resolved.Query.possibleOn
  simp only [Resolved.statementContext_initial_irrelevant clock counters parameters database subqueries first second nested,
    Resolved.Query.source_initial_irrelevant (query := query) (database := database) (first := first)
      (second := second) (own := own)]

/-- For every query, clock value, counters, values, two databases, subqueries and optional initial database,
a query and subqueries with no current table and no pragma source give the same results that SQLite may
give whichever current database is given. In plain words: the rows of {lit}`before.t` do not
change when the current database changes. -/
theorem Resolved.Query.possibleOn_current_irrelevant (query : Resolved.Query) (clock : Int) (counters : Counters)
    (parameters : List Value) (first second : Database) (subqueries : List Resolved.Query) (initial : Option Database)
    (own : query.readsCurrent = false) (nested : ∀ other ∈ subqueries, other.readsCurrent = false) :
    query.possibleOn clock counters parameters first subqueries initial =
      query.possibleOn clock counters parameters second subqueries initial := by
  unfold Resolved.Query.possibleOn
  simp only [Resolved.statementContext_current_irrelevant clock counters parameters first second subqueries initial nested,
    Resolved.Query.source_current_irrelevant (query := query) (first := first) (second := second)
      (initial := initial) (own := own)]

/-- For every clock value, counters, values, statement, database and two optional initial databases,
a statement with no source in the initial database has the same run whichever initial database is given
({name}`runStatement`). Proof sketch: a query runs by {name}`Resolved.Query.runOn_initial_irrelevant`; every other
statement does not use the initial database. -/
theorem runStatement_initial_irrelevant (clock : Int) (counters : Counters) (parameters : List Value)
    (statement : Resolved.Statement) (database : Database) (first second : Option Database)
    (plain : statement.readsInitial = false) :
    runStatement clock counters parameters statement database first =
      runStatement clock counters parameters statement database second := by
  cases statement
  case query query subqueries =>
    obtain ⟨own, nested⟩ := Resolved.Statement.readsInitial_query plain
    simp only [runStatement, Resolved.Query.runOn_initial_irrelevant query clock counters parameters database
      subqueries first second own nested]
  all_goals rfl

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
