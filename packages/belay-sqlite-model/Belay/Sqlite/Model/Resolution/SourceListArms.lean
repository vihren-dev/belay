import Belay.Sqlite.Model.Resolution.SourceList

set_option doc.verso true

/-! The equations of the resolution of pending sources in the shape that the functions had before the
name trace was threaded through them: proofs about {lit}`FROM` clauses unfold them with
{lit}`simp only [traced_arms]` and meet the same steps as before. -/

namespace Belay.Sqlite.Model

/-- A join without a condition resolves to no condition. -/
@[traced_arms] theorem resolveJoinCondition_none (dqs : Bool) (scope : Scope) (index : Nat) :
    resolveJoinCondition dqs scope index .none = .ok none := rfl

/-- A merged condition resolves to itself. -/
@[traced_arms] theorem resolveJoinCondition_merged (dqs : Bool) (scope : Scope) (index : Nat)
    (condition : Resolved.Expr) : resolveJoinCondition dqs scope index (.merged condition) = .ok (some condition) := rfl

/-- For every written condition: it resolves over the whole scope, and must then read only the sources
up to its own. Proof sketch: unfold the traced form and push the projection through the monad. -/
@[traced_arms] theorem resolveJoinCondition_written (dqs : Bool) (scope : Scope) (index : Nat) (path : List Nat)
    (term : Syntax.Expr) : resolveJoinCondition dqs scope index (.written path term) = (do
    let resolved ← condition path (resolveOperand dqs scope {} true term)
    let bound := scope.cellsBefore (index + 1)
    if resolved.readsBelow bound then pure (some resolved)
    else throw (.restriction path .laterTableInOn)) := by
  simp only [resolveJoinCondition, resolveJoinConditionTraced, resolveOperand, traced_drop]

/-- For every list of pending sources: the {lit}`ON` conditions resolve first, then the sources with
the arguments of each {lit}`json_each`. Proof sketch: unfold the traced form, push the projection
through the monad, and split on the item of each source. -/
@[traced_arms] theorem resolvePendingSources_arm (dqs : Bool) (scope : Scope) (sources : List PendingSource) :
    resolvePendingSources dqs scope sources = (do
    let conditions ← resolveAll (fun index (source : PendingSource) =>
      resolveJoinCondition dqs scope index source.condition) sources
    resolveAll (fun index ((source : PendingSource), condition) => do
      let resolved ← match source.item with
        | .table position => pure (Resolved.Source.table position)
        | .initialTable position => pure (Resolved.Source.initialTable position)
        | .each path arguments => resolveEachArguments dqs scope index path arguments
        | .pragma rows => pure (Resolved.Source.pragma rows)
        | .subquery index width => pure (Resolved.Source.subquery index width)
      pure { kind := source.kind, source := resolved, condition }) (sources.zip conditions)) := by
  simp only [resolvePendingSources, resolvePendingSourcesTraced, resolveJoinCondition, traced_drop]
  congr 1
  funext conditions
  congr 1
  funext index pair
  obtain ⟨source, condition⟩ := pair
  cases source.item <;> simp only [traced_drop, resolveEachArguments]

end Belay.Sqlite.Model
