import Belay.Sqlite.Model.Queries.Preparation.CountSelectResolution
import Belay.Sqlite.Model.Queries.Select.SubquerySelectResolution
import Belay.Sqlite.Model.Queries.Evaluation.StatementCalm

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The whole-table aggregate query of the given sources, {lit}`WHERE` condition, aggregate and result name: an aggregate
query of one group with the one result column the aggregate, and without grouping, ordering, window, {lit}`HAVING`,
{lit}`DISTINCT` or compound, that reads no cell of an outer query, and whose deciding call is the aggregate when it
is {lit}`min` or {lit}`max` ({name}`Resolved.Aggregate.minOrMax`). For example, {lit}`SELECT sum(c) FROM t` is
the whole-table aggregate query of the table, no condition, the aggregate {lit}`sum` of the column {lit}`c`. -/
def Resolved.Query.aggregateOf (sources : List Resolved.QuerySource) (filter : Option Resolved.Expr)
    (aggregate : Resolved.Aggregate) (name : String) : Resolved.Query :=
  { sources, filter, aggregate := true, groupBy := [], columns := [.aggregate aggregate], names := [name],
    orderBy := [], offset := 0, limit := none, limitParameter := none, offsetParameter := none, outer := 0,
    aggregates := [], having := none, distinct := none, deciding := aggregate.minOrMax }

/-- For every subquery shapes that have zero outer cells ({lit}`shapes.outer = 0`): the result column {lit}`agg(x)`,
where the name {lit}`agg` names an aggregate of one operand ({name}`aggregateNamed`) that does not write JSON and the
operand {lit}`x` resolves ({name}`resolveOperand`) to an expression, resolves to that aggregate of the resolved operand,
with the collation of the operand (only {lit}`min` and {lit}`max` use it), named by its alias or else its text, with no
affinity. Proof sketch: unfold the resolver; the name gives the aggregate, and the operand resolves by the hypothesis. -/
theorem resolveColumns_aggregate (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (name : String)
    (operand : Syntax.Expr) (alias : Option Identifier) (text : String)
    (build : Resolved.Expr → Resolved.Aggregate) (named : aggregateNamed name = some build) (resolved : Resolved.Expr)
    (affinity : Option Affinity) (operandOk : resolveOperand dqs scope shapes true operand = .ok (resolved, affinity))
    (outerZero : shapes.outer = 0) (noJson : (build resolved).writesJson = false) :
    resolveAll (resolveResultColumn dqs scope shapes) [.expression (.call name [operand]) alias text] =
      .ok [[(.aggregate ((build resolved).withCollation (operand.collationIn scope)), (alias.map (·.text)).getD text,
        none)]] := by
  have notJson : ¬ (build resolved).writesJson = true := by simp [noJson]
  simp [resolveAll, resolveAllFrom, resolveResultColumn_expression, resolveResultColumn_star, resolveResultColumn_sourceStar, named, operandOk, outerZero, notJson, Resolved.Expr.readsUnder,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- For every query whose one result column is an aggregate call, without grouping, ordering and {lit}`HAVING`, and
whose call resolves to the aggregate {lit}`a`, the deciding call is {lit}`a` when it is {lit}`min` or {lit}`max`
({name}`Resolved.Aggregate.minOrMax`), and none otherwise. Proof sketch: the query's one call is the
result column itself, so it is listed once and resolves to the output {lit}`a`; then split on whether
{lit}`a` is {lit}`min` or {lit}`max`. -/
theorem decidingCall_aggregateColumn (scope : Scope) (source : Option Syntax.TableReference)
    (filter : Option Syntax.Expr) (name : String) (operand : Syntax.Expr) (alias : Option Identifier) (text : String)
    (called : aggregateCall (.call name [operand]) = true) (a : Resolved.Aggregate) :
    decidingCall scope (Syntax.Subquery.mk [.expression (.call name [operand]) alias text] source [] filter [] [] none none none
        none false none none) [] [] (writtenResults scope [.expression (.call name [operand]) alias text]) [.aggregate a] =
      a.minOrMax := by
  cases minMax : a.minOrMax <;>
    simp [decidingCall, writtenResults, Syntax.Expr.indexIn, Syntax.Expr.aggregateCalls, called, Syntax.Expr.same_self,
      minMax]

/-- For every query {lit}`SELECT agg(x) FROM … WHERE p` without join, grouping, ordering, window, {lit}`HAVING`,
{lit}`DISTINCT` and compound, whose aggregate {lit}`agg` is one of one operand that does not write JSON
({name}`aggregateNamed`), whose operand, pending sources and {lit}`WHERE` condition resolve, the body resolves to the
whole-table aggregate query of its sources and condition ({name}`Resolved.Query.aggregateOf`), named by the alias of
its result column or else its text, with no affinity. Proof sketch: unfold the resolver; the query is an aggregate
query, the call is the result column itself, so it lists no aggregate, and every clause that the query lacks
resolves to its empty form; then follow the steps with the hypotheses. -/
theorem resolveQueryBody_aggregate (dqs : Bool) (scope : Scope) (current : Option Nat) (later : List SubqueryShape)
    (outerAliases : List Identifier) (pending : List PendingSource) (source : Option Syntax.TableReference)
    (filter : Option Syntax.Expr) (name : String) (operand : Syntax.Expr) (alias : Option Identifier) (text : String)
    (build : Resolved.Expr → Resolved.Aggregate) (named : aggregateNamed name = some build) (resolved : Resolved.Expr)
    (affinity : Option Affinity)
    (operandOk : resolveOperand dqs scope { current, later } true operand = .ok (resolved, affinity))
    (noJson : (build resolved).writesJson = false) (condition : Option Resolved.Expr)
    (sources : List Resolved.QuerySource)
    (resolves : FilterResolves dqs scope
      ((resultAliases scope [.expression (.call name [operand]) alias text]).filterMap id ++ outerAliases)
      filter condition { current, later })
    (pendingOk : resolvePendingSources dqs scope pending = .ok sources) :
    resolveQueryBody dqs scope { current, later } outerAliases pending
        (Syntax.Subquery.mk [.expression (.call name [operand]) alias text] source [] filter [] [] none none none none
          false none none) =
      .ok (Resolved.Query.aggregateOf sources condition
        ((build resolved).withCollation (operand.collationIn scope)) ((alias.map (·.text)).getD text), none) := by
  have called : aggregateCall (.call name [operand]) = true := by simp [aggregateCall, named]
  have columns := resolveColumns_aggregate dqs scope { current, later } name operand alias text build named resolved
    affinity operandOk rfl noJson
  have aggregates : (Syntax.Expr.call name [operand]).aggregateCalls = [.call name [operand]] := by
    simp [Syntax.Expr.aggregateCalls, called]
  rw [resolveQueryBody_arm]
  dsimp only
  have nothing : ∀ {α β : Type} (f : Nat → α → Except ValueIssue β), resolveAll f [] = .ok [] := fun f => by
    simp [resolveAll, resolveAllFrom]
  simp only [List.any_cons, List.any_nil, Bool.or_false, aggregates, List.isEmpty_cons, Bool.not_false, Bool.not_true, called,
    List.isEmpty_nil, Bool.or_true, ite_true, Bool.false_and, Bool.true_and, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Option.toList_none, Syntax.Expr.distinctList, List.foldl_nil, Bool.not_eq_true',
    columns, nothing, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rcases resolves with ⟨found, rfl⟩ | ⟨term, expression, affinity, found, rfl, names, ok⟩
  · simp [aliasJoinItem?, found, pendingOk, windowValue, windowSkipsFailure, groupedOutput, Resolved.Query.aggregateOf,
      Resolved.Output.canFail, firstRowResults, decidingCall_aggregateColumn scope source _ name operand alias text called]
  · simp [aliasJoinItem?, found, pendingOk, names, ok, windowValue, windowSkipsFailure, groupedOutput, Resolved.Query.aggregateOf,
      Model.condition, Functor.map, Except.map, Resolved.Output.canFail, firstRowResults,
      decidingCall_aggregateColumn scope source _ name operand alias text called]

/-- For every condition and aggregate whose expressions are calm ({name}`Resolved.Expr.Calm`) and every position, the
statement of the whole-table aggregate query of the first source of a table is calm
({name}`Resolved.Statement.Calm`): the first source of a table has no expression, so the expressions of the
statement are the condition and the operands of the aggregate. Proof sketch: list the expressions of the query. -/
theorem Resolved.Statement.Calm.aggregateOf_first (position : Nat) (condition : Option Resolved.Expr)
    (aggregate : Resolved.Aggregate) (name : String) (conditionCalm : ∀ expression ∈ condition.toList, expression.Calm)
    (operandsCalm : ∀ expression ∈ (Resolved.Output.aggregate aggregate).operands, expression.Calm) :
    (Resolved.Statement.query
      (Resolved.Query.aggregateOf [Resolved.QuerySource.first position] condition aggregate name) []).Calm := by
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.expressions, Resolved.Query.keptExpressions,
    Resolved.Query.aggregateOf, Resolved.QuerySource.first, Resolved.QuerySource.expressions, List.mem_append,
    List.mem_flatMap, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false] at member
  simp only [Resolved.Output.scalars, List.map_nil, List.not_mem_nil, or_false] at member
  rcases member with (member | ⟨_, rfl, member | member⟩) | member
  · exact conditionCalm expression member
  · simp at member
  · simp at member
  · simp_all

end Belay.Sqlite.Model
