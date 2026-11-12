import Belay.Sqlite.Model.Queries.Select.DuplicateKeyGroupTerm
import Belay.Sqlite.Model.Queries.Evaluation.DuplicateKeyQuery

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every query of one result column {lit}`c` that calls no aggregate, grouped by one term, with {lit}`HAVING
count(*) > 1` and no {lit}`ORDER BY`, whose one aggregate {lit}`count(*)` resolves to {name}`Resolved.Aggregate.countRows`,
the query has no deciding call. Proof sketch: the result column has no aggregate call and the only
call, {lit}`count(*)`, is not {lit}`min` or {lit}`max`, so no call can decide the row. -/
theorem decidingCall_duplicateKeys (scope : Scope) (source : Option Syntax.TableReference) (value : Syntax.Expr)
    (text : String) (filter : Option Syntax.Expr) (term : Syntax.Expr) (name : String) (count : normalizeIdentifier name = "count")
    (noCalls : value.aggregateCalls = []) (outputs : List Resolved.Output) :
    decidingCall scope (Syntax.Subquery.mk [.expression value none text] source [] filter [term] [] none none none
        (some (.compare .gt (.callStar name) (.numeric "1"))) false none none) [.callStar name] [.countRows]
      (writtenResults scope [.expression value none text]) outputs = none := by
  simp [decidingCall, noCalls, Syntax.Expr.aggregateCalls, aggregateCall, count, Syntax.Expr.indexIn, Syntax.Expr.same_self,
    Resolved.Aggregate.minOrMax]

/-- For every query {lit}`SELECT c FROM … [WHERE w] GROUP BY k HAVING count(*) > 1` without join, ordering and window,
whose result column {lit}`c` has no alias, calls no aggregate and resolves to a column that the grouping key
covers ({name}`Resolved.Expr.grouped`) and that feeds no aggregate value to a fallible call, whose scope has only own
sources ({name}`Scope.ownSources`), whose pending sources resolve, whose {lit}`WHERE` condition resolves as {name}`FilterResolves` says (it names no alias) and whose grouping
term resolves ({name}`GroupTermResolvesIn`) with the aggregate call {lit}`count(*)`, the body resolves to the
duplicate-key query of its sources, condition, result column, key and collation ({name}`Resolved.Query.duplicateKeys`),
with the affinity of the result column. With the literal {lit}`1` as the column and no {lit}`WHERE`, this is the query
of S4. Proof sketch: unfold the resolver; the query is an aggregate query whose one aggregate is the call of
{lit}`HAVING`, {name}`resolveOperand_moreThanOne` gives {lit}`HAVING`, the hypotheses give the other clauses, and every
clause that the query lacks resolves to its empty form. -/
theorem resolveQueryBody_duplicateKeys (dqs : Bool) (scope : Scope) (current : Option Nat) (later : List SubqueryShape)
    (outerAliases : List Identifier) (pending : List PendingSource) (source : Option Syntax.TableReference)
    (value : Syntax.Expr) (text : String) (filter : Option Syntax.Expr) (term : Syntax.Expr) (name : String)
    (count : normalizeIdentifier name = "count") (column : Resolved.Expr) (columnName : String)
    (affinity : Option Affinity) (key : Resolved.Expr) (collation : Collation) (sources : List Resolved.QuerySource)
    (whereCondition : Option Resolved.Expr) (notCall : aggregateCall value = false) (noCalls : value.aggregateCalls = [])
    (columnResolves : resolveAll (resolveResultColumn dqs scope { current, later, aggregates := [.callStar name] })
      [.expression value none text] = .ok [[(.scalar column, columnName, affinity)]])
    (columnGrouped : column.grouped [key] = true)
    (columnFeeds : (column.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false)
    (filterResolves : FilterResolves dqs scope outerAliases filter whereCondition
      { current, later, aggregates := [.callStar name] })
    (groupResolves : GroupTermResolvesIn dqs scope { current, later, aggregates := [.callStar name] }
      (.scalar column, columnName, affinity) (value.collationIn scope) term key collation)
    (own : scope.ownSources = scope)
    (pendingOk : resolvePendingSources dqs scope pending = .ok sources) :
    resolveQueryBody dqs scope { current, later } outerAliases pending
        (Syntax.Subquery.mk [.expression value none text] source [] filter [term] [] none none none
          (some (.compare .gt (.callStar name) (.numeric "1"))) false none none) =
      .ok (Resolved.Query.duplicateKeys sources whereCondition column columnName key collation, affinity) := by
  have called : aggregateCall (.callStar name) = true := by simp [aggregateCall, count]
  have havingCalls : (Syntax.Expr.compare .gt (.callStar name) (.numeric "1")).aggregateCalls = [.callStar name] := by
    simp [Syntax.Expr.aggregateCalls, aggregateCall, count]
  have calls : Syntax.Expr.distinctList [.callStar name] = [.callStar name] := by simp [Syntax.Expr.distinctList]
  have aggregates : resolveAll (fun _ call => resolveAggregateCall dqs scope { current, later, aggregates := [.callStar name] } call)
      [.callStar name] = .ok [.countRows] := by
    simp [resolveAll, resolveAllFrom, resolveAggregateCall_callStar, Bind.bind, Except.bind, Pure.pure, Except.pure]
  have aliases : resultAliases scope [.expression value none text] = [none] := by simp [resultAliases]
  have collations : resultCollations scope [.expression value none text] = [value.collationIn scope] := by
    simp [resultCollations]
  have terms : resolveAll (resolveGroupTerm dqs scope { current, later, aggregates := [.callStar name] } [none]
      [(.scalar column, columnName, affinity)] [value.collationIn scope]) [term] = .ok [(key, collation)] := by
    simp [resolveAll, resolveAllFrom, show resolveGroupTerm dqs scope { current, later, aggregates := [.callStar name] } [none]
      [(.scalar column, columnName, affinity)] [value.collationIn scope] 0 term = .ok (key, collation) from groupResolves,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
  have names : ∀ list, namesAlias scope list (.compare .gt (.callStar name) (.numeric "1")) = false := by
    intro list; simp [namesAlias]
  have having := resolveOperand_moreThanOne dqs scope { current, later, aggregates := [.callStar name] } name rfl
  have outputGrouped : groupedOutput [key] (.scalar column) = true := columnGrouped
  rw [resolveQueryBody_arm]
  dsimp only
  simp only [aliasJoinItem?, List.zipIdx_nil, List.find?_nil, Option.map_none, notCall, noCalls, havingCalls, calls, Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.isEmpty_cons, List.isEmpty_nil, List.any_cons, List.any_nil, Bool.false_or, Bool.not_false, Bool.true_or, Bool.false_eq_true, ↓reduceIte, List.nil_append, Bool.not_true, Bool.and_false]
  have nothing : ∀ {α β : Type} (f : Nat → α → Except ValueIssue β), resolveAll f [] = .ok [] := fun f => by
    simp [resolveAll, resolveAllFrom]
  have havingFeeds : ((Resolved.Expr.compare .gt none (.aggregateValue 0) (.literal (.integer 1)) .binary).any
      fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false := by
    simp [Resolved.Expr.any, Resolved.Expr.isFallibleCall]
  rcases filterResolves with ⟨rfl, rfl⟩ | ⟨filterTerm, expression, filterAffinity, rfl, rfl, filterNames, filterOk⟩
  · simp only [own, columnResolves, pendingOk, aliases, collations, List.flatten_cons, List.flatten_nil, List.append_nil,
      aggregates, terms, names, having, Bind.bind, Except.bind, Pure.pure, Except.pure]
    simp [nothing, condition, outputGrouped, windowSkipsFailure, windowValue, Resolved.Expr.grouped,
      Resolved.Query.duplicateKeys, decidingCall_duplicateKeys scope source value text _ term name count noCalls]
    exact ⟨columnFeeds, havingFeeds⟩
  · simp only [own, columnResolves, pendingOk, aliases, collations, List.flatten_cons, List.flatten_nil, List.append_nil,
      aggregates, terms, names, having, filterOk, Bind.bind, Except.bind, Pure.pure, Except.pure]
    simp [nothing, condition, outputGrouped, windowSkipsFailure, windowValue, filterNames,
      Resolved.Expr.grouped, Resolved.Query.duplicateKeys, decidingCall_duplicateKeys scope source value text _ term name count noCalls]
    exact ⟨columnFeeds, havingFeeds⟩

/-- The result column {lit}`1` meets the conditions of {name}`resolveQueryBody_duplicateKeys` on the result column: it is
no aggregate call, it calls no aggregate, it resolves in any scope to the literal one named {lit}`"1"` with no affinity,
every grouping key covers it, and it feeds no aggregate value to a fallible call. Proof sketch: the definitions
compute; {name}`resolveColumns_one` resolves the column. -/
theorem resultColumn_one_facts (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (key : Resolved.Expr) :
    aggregateCall (.numeric "1") = false ∧ (Syntax.Expr.numeric "1").aggregateCalls = [] ∧
    resolveAll (resolveResultColumn dqs scope shapes) [.expression (.numeric "1") none "1"] =
      .ok [[(.scalar (.literal (.integer 1)), "1", none)]] ∧
    (Resolved.Expr.literal (.integer 1)).grouped [key] = true ∧
    ((Resolved.Expr.literal (.integer 1)).any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) =
      false :=
  ⟨by simp [aggregateCall], by simp [Syntax.Expr.aggregateCalls, aggregateCall], resolveColumns_one dqs scope shapes,
    by simp [Resolved.Expr.grouped], by simp [Resolved.Expr.any, Resolved.Expr.isFallibleCall]⟩

end Belay.Sqlite.Model
