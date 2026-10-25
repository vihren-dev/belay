import Belay.Sqlite.Model.TwoStateReads

set_option doc.verso true

/-! A query that reads only the initial database does not depend on the current database
(ADR 0017, S6). These laws mirror {lit}`TwoStateReads.lean` with the roles of the two databases
exchanged: {name}`Belay.Sqlite.Model.Resolved.Query.readsCurrent` tells whether a query reads
the current database. They show that the rows of {lit}`before.t` do not change when the current
database changes, whatever the names, positions and schemas of its tables. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every context, two databases, optional initial database, rows so far and join, a source that
does not read the current database joins the same rows whichever current database is given. Proof
sketch: split on the source; the cases that read no current database do not mention it. -/
theorem QuerySource.join_current_irrelevant (context : EvalContext) (first second : Database)
    (initial : Option Database) (state : SourceRows) (join : QuerySource)
    (plain : join.source.readsCurrent = false) :
    QuerySource.join context first initial state join = QuerySource.join context second initial state join := by
  obtain ⟨kind, source, condition⟩ := join
  cases source <;> first | rfl | simp [Source.readsCurrent] at plain

/-- For every context, two databases, optional initial database and list of sources that read no current
database, the fold of the joins from any rows so far is the same for both databases. Proof sketch:
induction on the sources with {name}`QuerySource.join_current_irrelevant`. -/
theorem foldlM_join_current_irrelevant (context : EvalContext) (first second : Database) (initial : Option Database) :
    ∀ (sources : List QuerySource) (state : SourceRows), sources.any (·.source.readsCurrent) = false →
      sources.foldlM (QuerySource.join context first initial) state =
        sources.foldlM (QuerySource.join context second initial) state
  | [], _, _ => rfl
  | join :: rest, state, plain => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at plain
    simp only [List.foldlM, QuerySource.join_current_irrelevant context first second initial state join plain.1]
    cases QuerySource.join context second initial state join with
    | none => rfl
    | some next => exact foldlM_join_current_irrelevant context first second initial rest next plain.2

/-- For every context, query, two databases and optional initial database, a query that reads no
current table has the same source rows whichever current database is given ({name}`Query.source`). Proof sketch: {name}`foldlM_join_current_irrelevant` on the sources of the query. -/
theorem Query.source_current_irrelevant (context : EvalContext) (query : Query) (first second : Database)
    (initial : Option Database) (own : query.readsCurrent = false) :
    query.source context first initial = query.source context second initial :=
  foldlM_join_current_irrelevant context first second initial query.sources _ own

/-- As {name}`Query.source_current_irrelevant`, for the source rows of a subquery after an outer
row ({name}`Query.sourceAfter`). Proof sketch: the same fold of the joins, started from the outer row. -/
theorem Query.sourceAfter_current_irrelevant (context : EvalContext) (outer : List Value) (query : Query)
    (first second : Database) (initial : Option Database) (own : query.readsCurrent = false) :
    query.sourceAfter context outer first initial = query.sourceAfter context outer second initial :=
  foldlM_join_current_irrelevant context first second initial query.sources _ own

/-- For every context, outer row, query, two databases and optional initial database, the run of a
subquery that reads no current table is the same whichever current database is given
({name}`Query.subqueryRun`). Proof sketch: unfold the run and rewrite its source rows with
{name}`Query.sourceAfter_current_irrelevant`. -/
theorem Query.subqueryRun_current_irrelevant (context : EvalContext) (outer : List Value) (query : Query)
    (first second : Database) (initial : Option Database) (own : query.readsCurrent = false) :
    query.subqueryRun context first outer initial = query.subqueryRun context second outer initial := by
  unfold Query.subqueryRun
  rw [Query.sourceAfter_current_irrelevant context outer query first second initial own]

/-- For every clock value, counters, values, two databases, subqueries that read no current table,
optional initial database and depth, the context of the subqueries is the same whichever current
database is given ({name}`subqueryContext`). Proof sketch: as
{name}`subqueryContext_initial_irrelevant`, by induction on the depth. -/
theorem subqueryContext_current_irrelevant (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (subqueries : List Query) (initial : Option Database)
    (plain : ∀ query ∈ subqueries, query.readsCurrent = false) :
    ∀ depth : Nat, subqueryContext clock counters parameters first subqueries initial depth =
      subqueryContext clock counters parameters second subqueries initial depth
  | 0 => rfl
  | depth + 1 => by
    have below := subqueryContext_current_irrelevant clock counters parameters first second subqueries initial plain depth
    simp only [subqueryContext, below]
    congr 1
    funext index outer
    cases found : subqueries[index]? with
    | none => rfl
    | some query =>
      simp only []
      exact Query.subqueryRun_current_irrelevant _ outer query first second initial
        (plain query (List.mem_of_getElem? found))

/-- For every clock value, counters, values, two databases, subqueries that read no current table and
optional initial database, the context of a statement is the same whichever current database is
given ({name}`statementContext`). Proof sketch: it is the context at the depth that
{name}`subqueryContext_current_irrelevant` covers. -/
theorem statementContext_current_irrelevant (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (subqueries : List Query) (initial : Option Database)
    (plain : ∀ query ∈ subqueries, query.readsCurrent = false) :
    statementContext clock counters parameters first subqueries initial =
      statementContext clock counters parameters second subqueries initial :=
  subqueryContext_current_irrelevant clock counters parameters first second subqueries initial plain _

end Belay.Sqlite.Model.Resolved
