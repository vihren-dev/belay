import Belay.Sqlite.Model.Resolution.Queries
import Belay.Sqlite.Model.Resolution.ScopeOwn

set_option doc.verso true

/-! The equation of {lit}`resolveQueryBody` in the shape that the function had before the name trace
was threaded through it: the proofs of the laws about a query body unfold it with
{lit}`simp only [traced_arms]` and meet the same steps as before. -/

namespace Belay.Sqlite.Model

/-- For every query body: it lists the aggregate calls of the query and resolves them, then the result
columns, {lit}`WHERE`, the sources, the grouping terms, {lit}`HAVING` and the ordering terms, and
checks the clauses against each other, exactly as {name}`resolveQueryBodyTraced` does without its
trace. Proof sketch: unfold both sides to the projection of the traced steps, push the projection
through the monad with {lit}`traced_drop`, and split on the alias test of each ordering term. -/
@[traced_arms] theorem resolveQueryBody_arm (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes)
    (outerAliases : List Identifier) (pending : List PendingSource) (query : Syntax.Subquery) :
    resolveQueryBody dqs scope shapes outerAliases pending query = (do
    let aggregate := !query.groupBy.isEmpty || query.columns.any fun
      | .expression value _ _ => !value.aggregateCalls.isEmpty
      | .star | .sourceStar _ => false
    let calls := (query.columns.flatMap (fun
        | .expression value _ _ => if aggregateCall value then [] else value.aggregateCalls
        | .star | .sourceStar _ => []) ++
      (if aggregate then query.having.toList.flatMap Syntax.Expr.aggregateCalls ++
        query.orderBy.flatMap (·.expression.aggregateCalls) else [])) |> Syntax.Expr.distinctList
    let shapes := { shapes with aggregates := calls }
    let aggregates ← resolveAll (fun _ call => resolveAggregateCall dqs scope shapes call) calls
    let outputs := (← resolveAll (resolveResultColumn dqs scope shapes) query.columns).flatten
    -- SQLite resolves the result columns before it checks HAVING.
    if query.having.isSome && !aggregate then throw (.prepare .havingNonAggregate)
    let aliases := resultAliases scope query.columns
    let visibleAliases := aliases.filterMap id ++ outerAliases
    let condition ← match query.filter with
      | none => pure none
      | some term =>
        if namesAlias scope visibleAliases term then throw (aliasInExpression.under [3])
        else do pure (some (← condition [3] (resolveOperand dqs scope shapes true term)))
    -- SQLite resolves a result column alias in an ON condition as it does in WHERE.
    if let some item := aliasJoinItem? scope visibleAliases query.joins then
      throw (aliasInExpression.under [2, item, 2])
    let sources ← resolvePendingSources dqs scope pending
    let collations := resultCollations scope query.columns
    let terms ← resolveAll (resolveGroupTerm dqs scope.ownSources shapes aliases outputs collations) query.groupBy
    if aggregate && !outputs.all (groupedOutput (terms.map Prod.fst) ·.1) then
      throw (.restriction [0] .bareColumn)
    let having ← match query.having with
      | none => pure none
      | some term =>
        if namesAlias scope visibleAliases term then throw (aliasInExpression.under [9])
        else
          let resolved ← Belay.Sqlite.Model.condition [9] (resolveOperand dqs scope shapes false term)
          if resolved.grouped (terms.map Prod.fst) then pure (some resolved) else throw (.restriction [9] .bareColumn)
    let order ← resolveAll (resolveOrderTerm dqs scope.ownSources shapes aliases visibleAliases outputs collations
      (terms.map Prod.fst) aggregate query.distinct) query.orderBy
    let feedsCall := fun (expression : Resolved.Expr) =>
      expression.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)
    let scalars := outputs.filterMap fun (output, _) => match output with
      | .scalar expression => some expression
      | .aggregate _ => none
    let sorted := order.filterMap fun term => match term.key with
      | .expression expression => some expression
      | .output _ => none
    if (scalars ++ having.toList ++ sorted).any feedsCall then
      throw (.restriction [] .aggregateInExpression)
    let (limitValue, limitParameter) ← windowValue [6] query.limit
    let (offsetValue, offsetParameter) ← windowValue [7] query.offset
    if offsetValue.any (· < 0) then throw (.restriction [7] .negativeOffset)
    if windowSkipsFailure query.groupBy query.limit query.offset (outputs.map (·.1) ++ aggregates.map .aggregate) then
      throw (.restriction [6] .windowedGroupSum)
    return ({ sources, filter := condition, aggregate, groupBy := terms,
              columns := outputs.map (·.1), names := outputs.map (·.2.1), orderBy := order,
              offset := (offsetValue.getD 0).toNat,
              limit := limitValue.bind fun value => if value < 0 then none else some value.toNat,
              limitParameter, offsetParameter,
              outer := shapes.outer, aggregates, having,
              distinct := if query.distinct then some collations else none }, (outputs.head?.bind (·.2.2)))
  ) := by
  cases hF : query.filter <;> cases hH : query.having <;>
  cases hJ : aliasJoinItem? scope ((resultAliases scope query.columns).filterMap id ++ outerAliases) query.joins <;>
  simp only [resolveQueryBody, resolveQueryBodyTraced, resolveAggregateCall,
    resolvePendingSources, traced_drop, hF, hH, hJ, Option.isSome_none, Option.isSome_some, Option.get_some, Bool.false_eq_true, dite_false, dite_true] <;>
  rfl

end Belay.Sqlite.Model
