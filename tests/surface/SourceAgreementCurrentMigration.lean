import Belay.Sqlite.Model.TwoStateStatementLaws

/-! Temporary migration witnesses for the exact source formulas at 3e2212ed.
Retire after final Nix acceptance; retain the accepted revision for replay. -/

namespace Belay.Sqlite.Model
open Resolved

/-- The original QuerySource.join_current_irrelevant formula follows from shared agreement. -/
example (context : EvalContext) (first second : Database)
    (initial : Option Database) (state : SourceRows) (join : QuerySource)
    (plain : join.source.readsCurrent = false) :
    QuerySource.join context first initial state join = QuerySource.join context second initial state join := by
  apply QuerySource.join_agrees context first second initial initial state join
  obtain ⟨kind, source, condition⟩ := join
  cases source <;> simp_all [Source.readsCurrent, Source.Agrees]

/-- The original foldlM_join_current_irrelevant formula follows from shared agreement. -/
example (context : EvalContext) (first second : Database) (initial : Option Database) :
    ∀ (sources : List QuerySource) (state : SourceRows), sources.any (·.source.readsCurrent) = false →
      sources.foldlM (QuerySource.join context first initial) state =
        sources.foldlM (QuerySource.join context second initial) state := by
  intro sources state plain
  apply foldlM_join_agrees context first second initial initial sources state
  intro join member
  have unread := List.any_eq_false.mp plain join member
  obtain ⟨kind, source, condition⟩ := join
  cases source <;> simp_all [Source.readsCurrent, Source.Agrees]

/-- The original Query.source_current_irrelevant formula follows from shared agreement. -/
example (context : EvalContext) (query : Query) (first second : Database)
    (initial : Option Database) (own : query.readsCurrent = false) :
    query.source context first initial = query.source context second initial :=
  Query.source_agrees context first second initial initial query
    (Query.Agrees.of_noCurrent first second initial query own)

/-- The original Query.sourceAfter_current_irrelevant formula follows from shared agreement. -/
example (context : EvalContext) (outer : List Value) (query : Query)
    (first second : Database) (initial : Option Database) (own : query.readsCurrent = false) :
    query.sourceAfter context outer first initial = query.sourceAfter context outer second initial :=
  Query.sourceAfter_agrees context first second initial initial outer query
    (Query.Agrees.of_noCurrent first second initial query own)

/-- The original Query.subqueryRun_current_irrelevant formula follows from shared agreement. -/
example (context : EvalContext) (outer : List Value) (query : Query)
    (first second : Database) (initial : Option Database) (own : query.readsCurrent = false) :
    query.subqueryRun context first outer initial = query.subqueryRun context second outer initial :=
  Query.subqueryRun_agrees context first second initial initial outer query
    (Query.Agrees.of_noCurrent first second initial query own)

/-- The original subqueryContext_current_irrelevant formula follows from shared agreement. -/
example (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (subqueries : List Query) (initial : Option Database)
    (plain : ∀ query ∈ subqueries, query.readsCurrent = false) :
    ∀ depth : Nat, subqueryContext clock counters parameters first subqueries initial depth =
      subqueryContext clock counters parameters second subqueries initial depth :=
  subqueryContext_agrees clock counters parameters first second subqueries initial initial
    (fun query member => Query.Agrees.of_noCurrent first second initial query (plain query member))

/-- The original statementContext_current_irrelevant formula follows from shared agreement. -/
example (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (subqueries : List Query) (initial : Option Database)
    (plain : ∀ query ∈ subqueries, query.readsCurrent = false) :
    statementContext clock counters parameters first subqueries initial =
      statementContext clock counters parameters second subqueries initial :=
  statementContext_agrees clock counters parameters first second subqueries initial initial
    (fun query member => Query.Agrees.of_noCurrent first second initial query (plain query member))

/-- The retained Resolved.Query.possibleOn_current_irrelevant formula keeps every original premise. -/
example (query : Resolved.Query) (clock : Int) (counters : Counters)
    (parameters : List Value) (first second : Database) (subqueries : List Resolved.Query) (initial : Option Database)
    (own : query.readsCurrent = false) (nested : ∀ other ∈ subqueries, other.readsCurrent = false) :
    query.possibleOn clock counters parameters first subqueries initial =
      query.possibleOn clock counters parameters second subqueries initial :=
  Resolved.Query.possibleOn_current_irrelevant query clock counters parameters first second subqueries initial own nested

end Belay.Sqlite.Model
