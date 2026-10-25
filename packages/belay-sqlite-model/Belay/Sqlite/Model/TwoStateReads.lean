import Belay.Sqlite.Model.Subqueries

set_option doc.verso true

/-! Which database a resolved query reads (ADR 0017, S6). A two-state query reads the current
database through the sources {name}`Belay.Sqlite.Model.Resolved.Source.table` and
{name}`Belay.Sqlite.Model.Resolved.Source.pragma`, and the fixed initial database through
{name}`Belay.Sqlite.Model.Resolved.Source.initialTable`. This file defines the two reads and proves
that the source rows, the run of a subquery and the context of a statement do not depend on a
database that the query does not read. {lit}`TwoStateStatementLaws.lean` lifts the laws to the
statement. -/

namespace Belay.Sqlite.Model.Resolved

/-- Whether a query has a source in the initial database ({name}`Source.isInitial`). The
subqueries of a statement are separate queries; {lit}`Statement.readsInitial` collects them. -/
def Query.readsInitial (query : Query) : Bool :=
  query.sources.any (·.source.isInitial)

/-- Whether a query has a source in the current database ({name}`Source.readsCurrent`). -/
def Query.readsCurrent (query : Query) : Bool :=
  query.sources.any (·.source.readsCurrent)

/-- For every context, database, two optional initial databases, rows so far and join, a source
that is not in the initial database joins the same rows whichever initial database is given.
In plain words: only the case {name}`Source.initialTable` of {name}`QuerySource.join` reads
{lit}`initial`. Proof sketch: split on the source; the other cases do not mention {lit}`initial`, so
both sides are equal by computation. -/
theorem QuerySource.join_initial_irrelevant (context : EvalContext) (database : Database)
    (first second : Option Database) (state : SourceRows) (join : QuerySource)
    (plain : join.source.isInitial = false) :
    QuerySource.join context database first state join = QuerySource.join context database second state join := by
  obtain ⟨kind, source, condition⟩ := join
  cases source <;> first | rfl | simp [Source.isInitial] at plain

/-- For every context, database, two optional initial databases and list of sources without a source in
the initial database, the fold of the joins from any rows so far is the same for both. Proof sketch:
induction on the sources with {name}`QuerySource.join_initial_irrelevant`. -/
theorem foldlM_join_initial_irrelevant (context : EvalContext) (database : Database) (first second : Option Database) :
    ∀ (sources : List QuerySource) (state : SourceRows), sources.any (·.source.isInitial) = false →
      sources.foldlM (QuerySource.join context database first) state =
        sources.foldlM (QuerySource.join context database second) state
  | [], _, _ => rfl
  | join :: rest, state, plain => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at plain
    simp only [List.foldlM, QuerySource.join_initial_irrelevant context database first second state join plain.1]
    cases QuerySource.join context database second state join with
    | none => rfl
    | some next => exact foldlM_join_initial_irrelevant context database first second rest next plain.2

/-- For every context, query, database and two optional initial databases, a query that reads no
initial table has the same source rows ({name}`Query.source`) whichever initial database is given. Proof sketch:
{name}`foldlM_join_initial_irrelevant` on the sources of the query. -/
theorem Query.source_initial_irrelevant (context : EvalContext) (query : Query) (database : Database)
    (first second : Option Database) (own : query.readsInitial = false) :
    query.source context database first = query.source context database second :=
  foldlM_join_initial_irrelevant context database first second query.sources _ own

/-- As {name}`Query.source_initial_irrelevant`, for the source rows of a subquery after an outer row
({name}`Query.sourceAfter`). Proof sketch: the same fold of the joins, started from the outer row. -/
theorem Query.sourceAfter_initial_irrelevant (context : EvalContext) (outer : List Value) (query : Query)
    (database : Database) (first second : Option Database) (own : query.readsInitial = false) :
    query.sourceAfter context outer database first = query.sourceAfter context outer database second :=
  foldlM_join_initial_irrelevant context database first second query.sources _ own

/-- For every context, outer row, query, database and two optional initial databases, the run of a
subquery that reads no initial table is the same whichever initial database is given
({name}`Query.subqueryRun`). Proof sketch: unfold the run and rewrite its source rows with
{name}`Query.sourceAfter_initial_irrelevant`. -/
theorem Query.subqueryRun_initial_irrelevant (context : EvalContext) (database : Database) (outer : List Value)
    (query : Query) (first second : Option Database) (own : query.readsInitial = false) :
    query.subqueryRun context database outer first = query.subqueryRun context database outer second := by
  unfold Query.subqueryRun
  rw [Query.sourceAfter_initial_irrelevant context outer query database first second own]

/-- For every clock value, counters, values, database, subqueries without a source in the initial
database, two optional initial databases and depth, the context of the subqueries is the same
whichever initial database is given ({name}`subqueryContext`). Proof sketch: induction on the depth;
each subquery runs in the context one depth below, which is equal by the hypothesis of the
induction, and {name}`Query.subqueryRun_initial_irrelevant` gives the run. -/
theorem subqueryContext_initial_irrelevant (clock : Int) (counters : Counters) (parameters : List Value)
    (database : Database) (subqueries : List Query) (first second : Option Database)
    (plain : ∀ query ∈ subqueries, query.readsInitial = false) :
    ∀ depth : Nat, subqueryContext clock counters parameters database subqueries first depth =
      subqueryContext clock counters parameters database subqueries second depth
  | 0 => rfl
  | depth + 1 => by
    have below := subqueryContext_initial_irrelevant clock counters parameters database subqueries first second plain depth
    simp only [subqueryContext, below]
    congr 1
    funext index outer
    cases found : subqueries[index]? with
    | none => rfl
    | some query =>
      simp only []
      exact Query.subqueryRun_initial_irrelevant _ database outer query first second
        (plain query (List.mem_of_getElem? found))

/-- For every clock value, counters, values, database, subqueries without a source in the initial
database and two optional initial databases, the context of a statement is the same whichever
initial database is given ({name}`statementContext`). Proof sketch: it is the context at the depth that
{name}`subqueryContext_initial_irrelevant` covers. -/
theorem statementContext_initial_irrelevant (clock : Int) (counters : Counters) (parameters : List Value)
    (database : Database) (subqueries : List Query) (first second : Option Database)
    (plain : ∀ query ∈ subqueries, query.readsInitial = false) :
    statementContext clock counters parameters database subqueries first =
      statementContext clock counters parameters database subqueries second :=
  subqueryContext_initial_irrelevant clock counters parameters database subqueries first second plain _

end Belay.Sqlite.Model.Resolved
