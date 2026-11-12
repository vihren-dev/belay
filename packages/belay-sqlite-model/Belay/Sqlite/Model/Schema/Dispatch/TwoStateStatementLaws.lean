import Belay.Sqlite.Model.Schema.Dispatch.SourceAgreement
import Belay.Sqlite.Model.Queries.Preparation.TwoStateStatementLaws
import Belay.Sqlite.Model.Schema.Dispatch.StatementStep

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every query, clock value, counters, values, database, subqueries and two optional initial
databases, a query and subqueries with no source in the initial database run the same whichever
initial database is given ({name}`Resolved.Query.runOn`). Proof sketch: apply {name}`Resolved.Query.runOn_agrees`
with the initial-origin agreement adapter. -/
theorem Resolved.Query.runOn_initial_irrelevant (query : Resolved.Query) (clock : Int) (counters : Counters)
    (parameters : List Value) (database : Database) (subqueries : List Resolved.Query) (first second : Option Database)
    (own : query.readsInitial = false) (nested : ∀ other ∈ subqueries, other.readsInitial = false) :
    query.runOn clock counters parameters database subqueries first =
      query.runOn clock counters parameters database subqueries second :=
  Resolved.Query.runOn_agrees query clock counters parameters database database subqueries first second
    (Resolved.Query.Agrees.of_noInitial database first second query own)
    (fun other member => Resolved.Query.Agrees.of_noInitial database first second other (nested other member))

/-- As {name}`Resolved.Query.runOn_initial_irrelevant`, for the results that SQLite may give
({name}`Resolved.Query.possibleOn`). Proof sketch: apply
{name}`Resolved.Query.possibleOn_agrees` with the initial-origin agreement adapter. -/
theorem Resolved.Query.possibleOn_initial_irrelevant (query : Resolved.Query) (clock : Int) (counters : Counters)
    (parameters : List Value) (database : Database) (subqueries : List Resolved.Query) (first second : Option Database)
    (own : query.readsInitial = false) (nested : ∀ other ∈ subqueries, other.readsInitial = false) :
    query.possibleOn clock counters parameters database subqueries first =
      query.possibleOn clock counters parameters database subqueries second :=
  Resolved.Query.possibleOn_agrees query clock counters parameters database database subqueries first second
    (Resolved.Query.Agrees.of_noInitial database first second query own)
    (fun other member => Resolved.Query.Agrees.of_noInitial database first second other (nested other member))

/-- For every query, clock value, counters, values, two databases, subqueries and optional initial database,
a query and subqueries with no current table and no pragma source give the same results that SQLite may
give whichever current database is given. In plain words: the rows of {lit}`before.t` do not
change when the current database changes. Proof sketch: apply
{name}`Resolved.Query.possibleOn_agrees` with the current-origin agreement adapter. -/
theorem Resolved.Query.possibleOn_current_irrelevant (query : Resolved.Query) (clock : Int) (counters : Counters)
    (parameters : List Value) (first second : Database) (subqueries : List Resolved.Query) (initial : Option Database)
    (own : query.readsCurrent = false) (nested : ∀ other ∈ subqueries, other.readsCurrent = false) :
    query.possibleOn clock counters parameters first subqueries initial =
      query.possibleOn clock counters parameters second subqueries initial :=
  Resolved.Query.possibleOn_agrees query clock counters parameters first second subqueries initial initial
    (Resolved.Query.Agrees.of_noCurrent first second initial query own)
    (fun other member => Resolved.Query.Agrees.of_noCurrent first second initial other (nested other member))

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

end Belay.Sqlite.Model
