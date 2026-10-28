import Belay.Sqlite.Model.TwoStateStatementLaws

/-! Temporary migration witnesses for the exact source formulas at 3e2212ed.
Retire after final Nix acceptance; retain the accepted revision for replay. -/

namespace Belay.Sqlite.Model
open Resolved

/-- The original QuerySource.join_initial_irrelevant formula follows from shared agreement. -/
example (context : EvalContext) (database : Database)
    (first second : Option Database) (state : SourceRows) (join : QuerySource)
    (plain : join.source.isInitial = false) :
    QuerySource.join context database first state join = QuerySource.join context database second state join := by
  apply QuerySource.join_agrees context database database first second state join
  obtain ⟨kind, source, condition⟩ := join
  cases source <;> simp_all [Source.isInitial, Source.Agrees]

/-- The original foldlM_join_initial_irrelevant formula follows from shared agreement. -/
example (context : EvalContext) (database : Database) (first second : Option Database) :
    ∀ (sources : List QuerySource) (state : SourceRows), sources.any (·.source.isInitial) = false →
      sources.foldlM (QuerySource.join context database first) state =
        sources.foldlM (QuerySource.join context database second) state := by
  intro sources state plain
  apply foldlM_join_agrees context database database first second sources state
  intro join member
  have unread := List.any_eq_false.mp plain join member
  obtain ⟨kind, source, condition⟩ := join
  cases source <;> simp_all [Source.isInitial, Source.Agrees]

/-- The original Query.source_initial_irrelevant formula follows from shared agreement. -/
example (context : EvalContext) (query : Query) (database : Database)
    (first second : Option Database) (own : query.readsInitial = false) :
    query.source context database first = query.source context database second :=
  Query.source_agrees context database database first second query
    (Query.Agrees.of_noInitial database first second query own)

/-- The original Query.sourceAfter_initial_irrelevant formula follows from shared agreement. -/
example (context : EvalContext) (outer : List Value) (query : Query)
    (database : Database) (first second : Option Database) (own : query.readsInitial = false) :
    query.sourceAfter context outer database first = query.sourceAfter context outer database second :=
  Query.sourceAfter_agrees context database database first second outer query
    (Query.Agrees.of_noInitial database first second query own)

/-- The original Query.subqueryRun_initial_irrelevant formula follows from shared agreement. -/
example (context : EvalContext) (database : Database) (outer : List Value)
    (query : Query) (first second : Option Database) (own : query.readsInitial = false) :
    query.subqueryRun context database outer first = query.subqueryRun context database outer second :=
  Query.subqueryRun_agrees context database database first second outer query
    (Query.Agrees.of_noInitial database first second query own)

/-- The original subqueryContext_initial_irrelevant formula follows from shared agreement. -/
example (clock : Int) (counters : Counters) (parameters : List Value)
    (database : Database) (subqueries : List Query) (first second : Option Database)
    (plain : ∀ query ∈ subqueries, query.readsInitial = false) :
    ∀ depth : Nat, subqueryContext clock counters parameters database subqueries first depth =
      subqueryContext clock counters parameters database subqueries second depth :=
  subqueryContext_agrees clock counters parameters database database subqueries first second
    (fun query member => Query.Agrees.of_noInitial database first second query (plain query member))

/-- The original statementContext_initial_irrelevant formula follows from shared agreement. -/
example (clock : Int) (counters : Counters) (parameters : List Value)
    (database : Database) (subqueries : List Query) (first second : Option Database)
    (plain : ∀ query ∈ subqueries, query.readsInitial = false) :
    statementContext clock counters parameters database subqueries first =
      statementContext clock counters parameters database subqueries second :=
  statementContext_agrees clock counters parameters database database subqueries first second
    (fun query member => Query.Agrees.of_noInitial database first second query (plain query member))

/-- The retained Resolved.Query.runOn_initial_irrelevant formula keeps every original premise. -/
example (query : Resolved.Query) (clock : Int) (counters : Counters)
    (parameters : List Value) (database : Database) (subqueries : List Resolved.Query) (first second : Option Database)
    (own : query.readsInitial = false) (nested : ∀ other ∈ subqueries, other.readsInitial = false) :
    query.runOn clock counters parameters database subqueries first =
      query.runOn clock counters parameters database subqueries second :=
  Resolved.Query.runOn_initial_irrelevant query clock counters parameters database subqueries first second own nested

/-- The retained Resolved.Query.possibleOn_initial_irrelevant formula keeps every original premise. -/
example (query : Resolved.Query) (clock : Int) (counters : Counters)
    (parameters : List Value) (database : Database) (subqueries : List Resolved.Query) (first second : Option Database)
    (own : query.readsInitial = false) (nested : ∀ other ∈ subqueries, other.readsInitial = false) :
    query.possibleOn clock counters parameters database subqueries first =
      query.possibleOn clock counters parameters database subqueries second :=
  Resolved.Query.possibleOn_initial_irrelevant query clock counters parameters database subqueries first second own nested

end Belay.Sqlite.Model
