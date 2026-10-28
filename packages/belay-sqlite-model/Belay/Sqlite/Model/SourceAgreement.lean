import Belay.Sqlite.Model.Execution
import Belay.Sqlite.Model.PossibleResults

set_option doc.verso true

/-! Agreement on query-source observations from the current and initial databases.
One join, source-fold and nesting argument preserves complete query observations. -/

namespace Belay.Sqlite.Model.Resolved

/-- For the given current databases, optional initial databases and source:
* A current table has equal optional {name}`Database.table` lookups, including shape and rows.
* An initial table has equal optional lookups through the initial databases.
* A pragma has equal optional {name}`PragmaRows.rowsOn` results, including unsupported results.
* JSON and derived sources impose no database condition; they use the common evaluation
  context and intermediate rows. For example, two absent table lookups agree. -/
def Source.Agrees (first second : Database) (before after : Option Database) : Source → Prop
  | .table position => first.table position = second.table position
  | .initialTable position => before.bind (·.table position) = after.bind (·.table position)
  | .pragma rows => PragmaRows.rowsOn first rows = PragmaRows.rowsOn second rows
  | .each .. | .subquery .. => True

/-- For the given database pairs and query, every source satisfies {name}`Source.Agrees`.
A query without sources imposes no condition. -/
def Query.Agrees (first second : Database) (before after : Option Database) (query : Query) : Prop :=
  ∀ join ∈ query.sources, Source.Agrees first second before after join.source

/-- Equal source observations give identical join steps, including missing-source failure,
outer-join widths and faults. Proof sketch: inspect the source and rewrite its lookup. -/
theorem QuerySource.join_agrees (context : EvalContext) (first second : Database)
    (before after : Option Database) (state : SourceRows) (join : QuerySource)
    (agree : Source.Agrees first second before after join.source) :
    QuerySource.join context first before state join = QuerySource.join context second after state join := by
  obtain ⟨kind, source, condition⟩ := join
  cases source <;> simp only [Source.Agrees] at agree <;>
    simp only [QuerySource.join, agree]

/-- A single traversal lifts source agreement through the optional join fold. Proof sketch:
rewrite its head step and use the induction hypothesis on a successful intermediate state. -/
theorem foldlM_join_agrees (context : EvalContext) (first second : Database) (before after : Option Database) :
    ∀ (sources : List QuerySource) (state : SourceRows),
      (∀ join ∈ sources, Source.Agrees first second before after join.source) →
      sources.foldlM (QuerySource.join context first before) state =
        sources.foldlM (QuerySource.join context second after) state
  | [], _, _ => rfl
  | join :: rest, state, agree => by
    simp only [List.foldlM, QuerySource.join_agrees context first second before after state join
      (agree join (by simp))]
    cases QuerySource.join context second after state join with
    | none => rfl
    | some next =>
      exact foldlM_join_agrees context first second before after rest next
        (fun member found => agree member (by simp [found]))

/-- For every common context and query whose source observations agree, the optional
source rows are equal. Proof sketch: {name}`foldlM_join_agrees` at the empty-row seed. -/
theorem Query.source_agrees (context : EvalContext) (first second : Database)
    (before after : Option Database) (query : Query) (agree : Query.Agrees first second before after query) :
    query.source context first before = query.source context second after :=
  foldlM_join_agrees context first second before after query.sources _ agree

/-- For every common context, outer row and query whose source observations agree,
the optional correlated source rows are equal. Proof sketch: {name}`foldlM_join_agrees`
at the normalized outer-row seed. -/
theorem Query.sourceAfter_agrees (context : EvalContext) (first second : Database)
    (before after : Option Database) (outer : List Value) (query : Query)
    (agree : Query.Agrees first second before after query) :
    query.sourceAfter context outer first before = query.sourceAfter context outer second after :=
  foldlM_join_agrees context first second before after query.sources _ agree

/-- Equal sources give equal complete subquery runs: faults, ending and all certainty
fields are retained. Proof sketch: rewrite the only database-dependent input. -/
theorem Query.subqueryRun_agrees (context : EvalContext) (first second : Database)
    (before after : Option Database) (outer : List Value) (query : Query)
    (agree : Query.Agrees first second before after query) :
    query.subqueryRun context first outer before = query.subqueryRun context second outer after := by
  unfold Query.subqueryRun
  rw [Query.sourceAfter_agrees context first second before after outer query agree]

/-- Agreement for every nested query gives equal contexts at every depth. Proof sketch:
induct on the nesting budget, then apply subquery-run agreement at each queried index. -/
theorem subqueryContext_agrees (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (queries : List Query) (before after : Option Database)
    (agree : ∀ query ∈ queries, Query.Agrees first second before after query) :
    ∀ depth : Nat,
      subqueryContext clock counters parameters first queries before depth =
        subqueryContext clock counters parameters second queries after depth
  | 0 => rfl
  | depth + 1 => by
    have below := subqueryContext_agrees clock counters parameters first second queries before after agree depth
    simp only [subqueryContext, below]
    congr 1
    funext index outer
    cases found : queries[index]? with
    | none => rfl
    | some query =>
      exact Query.subqueryRun_agrees _ first second before after outer query
        (agree query (List.mem_of_getElem? found))

/-- For every common clock, counters, parameters and query list whose source observations
agree, the statement contexts are equal. Proof sketch: {name}`subqueryContext_agrees`
at the query-list length. -/
theorem statementContext_agrees (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (queries : List Query) (before after : Option Database)
    (agree : ∀ query ∈ queries, Query.Agrees first second before after query) :
    statementContext clock counters parameters first queries before =
      statementContext clock counters parameters second queries after :=
  subqueryContext_agrees clock counters parameters first second queries before after agree _

/-- The full resolved run agrees when its main and nested sources agree. Proof sketch:
rewrite the common statement context and source rows, leaving the same evaluator. -/
theorem Query.runOn_agrees (query : Query) (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (queries : List Query) (before after : Option Database)
    (own : Query.Agrees first second before after query)
    (nested : ∀ other ∈ queries, Query.Agrees first second before after other) :
    query.runOn clock counters parameters first queries before =
      query.runOn clock counters parameters second queries after := by
  unfold Query.runOn
  simp only [statementContext_agrees clock counters parameters first second queries before after nested,
    Query.source_agrees _ first second before after query own]

/-- The permitted query results agree under the same source contract. Proof sketch:
rewrite context and source rows, including the absent-source case. -/
theorem Query.possibleOn_agrees (query : Query) (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (queries : List Query) (before after : Option Database)
    (own : Query.Agrees first second before after query)
    (nested : ∀ other ∈ queries, Query.Agrees first second before after other) :
    query.possibleOn clock counters parameters first queries before =
      query.possibleOn clock counters parameters second queries after := by
  unfold Query.possibleOn
  simp only [statementContext_agrees clock counters parameters first second queries before after nested,
    Query.source_agrees _ first second before after query own]

/-- Unread initial sources give agreement for any two initial databases. Proof sketch:
every source has a false initial-origin test, so only the unchanged current lookups remain. -/
theorem Query.Agrees.of_noInitial (database : Database) (before after : Option Database) (query : Query)
    (plain : query.readsInitial = false) : Query.Agrees database database before after query := by
  intro join member
  simp only [Query.readsInitial, List.any_eq_false] at plain
  have unread := plain join member
  obtain ⟨kind, source, condition⟩ := join
  cases source <;> simp_all [Source.isInitial, Source.Agrees]

/-- Unread current sources give agreement for any two current databases. Proof sketch:
the false test excludes both current tables and pragmas; other lookups are unchanged. -/
theorem Query.Agrees.of_noCurrent (first second : Database) (initial : Option Database) (query : Query)
    (plain : query.readsCurrent = false) : Query.Agrees first second initial initial query := by
  intro join member
  simp only [Query.readsCurrent, List.any_eq_false] at plain
  have unread := plain join member
  obtain ⟨kind, source, condition⟩ := join
  cases source <;> simp_all [Source.readsCurrent, Source.Agrees]

end Belay.Sqlite.Model.Resolved
