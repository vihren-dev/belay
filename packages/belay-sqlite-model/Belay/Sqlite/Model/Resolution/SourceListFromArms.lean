import Belay.Sqlite.Model.Resolution.SourceList

set_option doc.verso true

/-! The equation of {lit}`resolveSources` in the shape that the function had before the name trace was
threaded through it: proofs about the sources of {lit}`FROM` unfold it with {lit}`simp only [traced_arms]`
and meet the same steps as before. -/

namespace Belay.Sqlite.Model

/-- For every catalog, first source and joins: the sources of {lit}`FROM` resolve the first reference,
then the reference of each join in order with its check for {lit}`json_each`, then the joins in
order; more than {name}`maximumJoinTables` tables is SQLite's {lit}`at most 64 tables in a join`. Proof
sketch: unfold the traced form and push the projection through the monad. -/
@[traced_arms] theorem resolveSources_some (catalog : Catalog) (source : Syntax.TableReference)
    (joins : List Syntax.Join) (start : Nat)
    (queries : Nat → Except SourceIssue ScopeSource) (prefix_ : List Nat) (initial : Option Catalog) :
    resolveSources catalog (some source) joins start queries prefix_ initial = (do
      if joins.length + 1 > maximumJoinTables then throw (.value (.prepare .tooManyTables))
      let (firstItem, firstSource) ← resolveReference catalog [1] source queries prefix_ initial
      let operators := joins.map (joinOperator ·.operator)
      let joined ← resolveAll (fun item ((join : Syntax.Join), operator) => do
        let resolved ← resolveReference catalog [2, item, 1] join.source queries prefix_ initial
        let earlier := source :: (joins.take item).map (·.source)
        (functionJoinChecked (earlier.any (·.arguments.isSome)) item join operator).mapError
          (SourceIssue.value ∘ ValueIssue.under prefix_)
        pure resolved) (joins.zip operators)
      let placed := Scope.place (firstSource :: joined.map Prod.snd) start
      let (scope, conditions) ← (mergeJoins (operators.any rightOrFull) (placed.take 1) 0
        (joins.zip (operators.zip (placed.drop 1)))).mapError (SourceIssue.value ∘ ValueIssue.under prefix_)
      let first : PendingSource := { item := firstItem, kind := .inner, condition := .none }
      pure (first :: ((joined.map Prod.fst).zip conditions).map fun (item, kind, condition) => { item, kind, condition },
        scope)) := by
  simp only [resolveSources, resolveSourcesTraced, mergeJoins, traced_drop]

end Belay.Sqlite.Model
