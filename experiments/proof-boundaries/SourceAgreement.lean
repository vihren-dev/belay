import Belay.Sqlite.Model.Execution
import Belay.Sqlite.Model.PossibleResults

set_option doc.verso true

/-! Experiment: one observation boundary for sources in both database origins. -/

namespace ProofBoundaries

open Belay.Sqlite.Model Belay.Sqlite.Model.Resolved

/-- Agreement on exactly the database observations made by one source. Table lookup
equality retains absence and the complete table shape; pragma equality retains both
unsupported rows and database-dependent rows. Expression and derived sources use the
shared evaluation context instead. -/
def SourceAgrees (first second : Database) (before after : Option Database) : Source → Prop
  | .table position => first.table position = second.table position
  | .initialTable position => before.bind (·.table position) = after.bind (·.table position)
  | .pragma pragma => pragma.rowsOn first = pragma.rowsOn second
  | .each .. | .subquery .. => True

/-- Every source in this query has equal observations in the two database pairs. -/
def QueryAgrees (first second : Database) (before after : Option Database) (query : Query) : Prop :=
  ∀ join ∈ query.sources, SourceAgrees first second before after join.source

/-- Equal source observations give identical join steps, including missing-source failure,
outer-join widths and faults. Proof sketch: inspect the source and rewrite its lookup. -/
theorem join_agrees (context : EvalContext) (first second : Database)
    (before after : Option Database) (state : SourceRows) (join : QuerySource)
    (agree : SourceAgrees first second before after join.source) :
    QuerySource.join context first before state join = QuerySource.join context second after state join := by
  obtain ⟨kind, source, condition⟩ := join
  cases source <;> simp only [SourceAgrees] at agree <;>
    simp only [QuerySource.join, agree]

/-- A single traversal lifts source agreement through the optional join fold. Proof sketch:
rewrite its head step and use the induction hypothesis on a successful intermediate state. -/
theorem fold_agrees (context : EvalContext) (first second : Database) (before after : Option Database) :
    ∀ (sources : List QuerySource) (state : SourceRows),
      (∀ join ∈ sources, SourceAgrees first second before after join.source) →
      sources.foldlM (QuerySource.join context first before) state =
        sources.foldlM (QuerySource.join context second after) state
  | [], _, _ => rfl
  | join :: rest, state, agree => by
    simp only [List.foldlM, join_agrees context first second before after state join
      (agree join (by simp))]
    cases QuerySource.join context second after state join with
    | none => rfl
    | some next =>
      exact fold_agrees context first second before after rest next
        (fun member found => agree member (by simp [found]))

/-- Top-level source equality is the common fold at its empty-row seed. -/
theorem source_agrees (context : EvalContext) (first second : Database)
    (before after : Option Database) (query : Query) (agree : QueryAgrees first second before after query) :
    query.source context first before = query.source context second after :=
  fold_agrees context first second before after query.sources _ agree

/-- Correlated source equality is the same fold at the query's normalized outer-row seed. -/
theorem sourceAfter_agrees (context : EvalContext) (first second : Database)
    (before after : Option Database) (outer : List Value) (query : Query)
    (agree : QueryAgrees first second before after query) :
    query.sourceAfter context outer first before = query.sourceAfter context outer second after :=
  fold_agrees context first second before after query.sources _ agree

/-- Equal sources give equal complete subquery runs: faults, ending and all certainty
fields are retained. Proof sketch: rewrite the only database-dependent input. -/
theorem subqueryRun_agrees (context : EvalContext) (first second : Database)
    (before after : Option Database) (outer : List Value) (query : Query)
    (agree : QueryAgrees first second before after query) :
    query.subqueryRun context first outer before = query.subqueryRun context second outer after := by
  unfold Query.subqueryRun
  rw [sourceAfter_agrees context first second before after outer query agree]

/-- Agreement for every nested query gives equal contexts at every depth. Proof sketch:
induct on the nesting budget, then apply subquery-run agreement at each queried index. -/
theorem subqueryContext_agrees (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (queries : List Query) (before after : Option Database)
    (agree : ∀ query ∈ queries, QueryAgrees first second before after query) :
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
      exact subqueryRun_agrees _ first second before after outer query
        (agree query (List.mem_of_getElem? found))

/-- Statement contexts agree by using the common depth theorem at the query-list length. -/
theorem statementContext_agrees (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (queries : List Query) (before after : Option Database)
    (agree : ∀ query ∈ queries, QueryAgrees first second before after query) :
    statementContext clock counters parameters first queries before =
      statementContext clock counters parameters second queries after :=
  subqueryContext_agrees clock counters parameters first second queries before after agree _

/-- The full resolved run agrees when its main and nested sources agree. Proof sketch:
rewrite the common statement context and source rows, leaving the same evaluator. -/
theorem runOn_agrees (query : Query) (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (queries : List Query) (before after : Option Database)
    (own : QueryAgrees first second before after query)
    (nested : ∀ other ∈ queries, QueryAgrees first second before after other) :
    query.runOn clock counters parameters first queries before =
      query.runOn clock counters parameters second queries after := by
  unfold Query.runOn
  simp only [statementContext_agrees clock counters parameters first second queries before after nested,
    source_agrees _ first second before after query own]

/-- The permitted query results agree under the same source contract. Proof sketch:
rewrite context and source rows, including the absent-source case. -/
theorem possibleOn_agrees (query : Query) (clock : Int) (counters : Counters) (parameters : List Value)
    (first second : Database) (queries : List Query) (before after : Option Database)
    (own : QueryAgrees first second before after query)
    (nested : ∀ other ∈ queries, QueryAgrees first second before after other) :
    query.possibleOn clock counters parameters first queries before =
      query.possibleOn clock counters parameters second queries after := by
  unfold Query.possibleOn
  simp only [statementContext_agrees clock counters parameters first second queries before after nested,
    source_agrees _ first second before after query own]

#print axioms subqueryContext_agrees
#print axioms runOn_agrees
#print axioms possibleOn_agrees

end ProofBoundaries
