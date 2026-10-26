import Belay.Sqlite.Model.CountStatementResolution
import Belay.Sqlite.Model.DuplicateKeyGroupTerm
import Belay.Sqlite.Model.DuplicateKeyQuery
import Belay.Sqlite.Model.ExistsStatementResolution
import Belay.Sqlite.Model.ScalarSubqueryResolution
import Belay.Sqlite.Model.Resolution.QueryAggregatesArms
import Belay.Sqlite.Model.Resolution.QueryBodyArms
import Belay.Sqlite.Model.Resolution.ScopeOwn

set_option doc.verso true

/-! The resolution of {lit}`SELECT c FROM t [WHERE w] GROUP BY k HAVING count(*) > 1` (ADR 0017, S4 and S6): the body of the query
resolves to the duplicate-key query ({name}`Belay.Sqlite.Model.Resolved.Query.duplicateKeys`) of its resolved sources,
grouping key and collation. The lemma takes the resolved sources and grouping term as hypotheses, because the catalog
is free. -/

namespace Belay.Sqlite.Model

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
      Resolved.Query.duplicateKeys]
    exact ⟨columnFeeds, havingFeeds⟩
  · simp only [own, columnResolves, pendingOk, aliases, collations, List.flatten_cons, List.flatten_nil, List.append_nil,
      aggregates, terms, names, having, filterOk, Bind.bind, Except.bind, Pure.pure, Except.pure]
    simp [nothing, condition, outputGrouped, windowSkipsFailure, windowValue, filterNames,
      Resolved.Expr.grouped, Resolved.Query.duplicateKeys]
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

/-- For every statement {lit}`SELECT 1 WHERE NOT EXISTS (SELECT c FROM t [WHERE w] GROUP BY k HAVING count(*) > 1)` of a
table that the catalog of the state has at a position, without table-function arguments, where the result column
{lit}`c` (without alias), the condition {lit}`w` and the grouping term {lit}`k` resolve in the scope of the table as
{name}`resolveQueryBody_duplicateKeys` requires, resolution gives the simple query without source and with the
condition {lit}`NOT EXISTS` of subquery 0, and the duplicate-key query of the first source of the table as its one
subquery, and leaves the state as it is. With the literal {lit}`1` as the column and no {lit}`WHERE`, this is the
statement of S4. The source reference has no indexed query. The table reference names no schema: it is not a
{lit}`before.t` source. Proof sketch: {name}`resolveStatement_select_of_resolveSelect` and
{name}`resolveSelect_noFrom_one_subquery`; the subquery resolves by {name}`resolveQueryBody_duplicateKeys` in the scope
of its table ({name}`resolveSources_table`, {name}`resolvePendingSources_table`), and the statement's query by
{name}`resolveQueryBody_simple` in the empty scope with the shape of the subquery, as for the other forms of
{lit}`NOT EXISTS`. -/
theorem resolveStatement_selectOne_notExists_duplicateKeys (context : ResolveContext) (state : ResolveState)
    (reference : Syntax.TableReference) (value : Syntax.Expr) (text : String) (filter : Option Syntax.Expr)
    (term : Syntax.Expr) (name : String) (count : normalizeIdentifier name = "count")
    (position : Nat) (table : CatalogTable) (column : Resolved.Expr) (columnName : String) (affinity : Option Affinity)
    (key : Resolved.Expr) (collation : Collation) (whereCondition : Option Resolved.Expr)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : state.catalog.findTable reference.table = some (position, table))
    (notCall : aggregateCall value = false) (noCalls : value.aggregateCalls = [])
    (columnResolves : resolveAll (resolveResultColumn context.profile.dqsDml (tableScope state.catalog reference position table)
      { current := some 0, aggregates := [.callStar name] }) [.expression value none text] =
      .ok [[(.scalar column, columnName, affinity)]])
    (columnGrouped : column.grouped [key] = true)
    (columnFeeds : (column.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false)
    (filterResolves : FilterResolves context.profile.dqsDml (tableScope state.catalog reference position table) [] filter
      whereCondition { current := some 0, aggregates := [.callStar name] })
    (groupResolves : GroupTermResolvesIn context.profile.dqsDml (tableScope state.catalog reference position table)
      { current := some 0, aggregates := [.callStar name] } (.scalar column, columnName, affinity)
      (value.collationIn (tableScope state.catalog reference position table)) term key collation) :
    resolveStatement context state (.select [.expression (.numeric "1") none "1"] none [] (some (.not (.exists 0))) [] []
        none none
        [Syntax.Subquery.mk [.expression value none text] (some reference) [] filter [term] [] none none none
          (some (.compare .gt (.callStar name) (.numeric "1"))) false none none] none false none) =
      .ok (.query (Resolved.Query.selectOneWhere (.not (.exists 0)))
        [Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] whereCondition column columnName key collation],
        state) := by
  have simple : ∀ source filter, (Syntax.Subquery.mk [.expression (.numeric "1") none "1"] source [] filter [] [] none none
      none none false none none).Simple := fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have noFeed : (([[(Resolved.Output.scalar (.literal (.integer 1)), "1", (none : Option Affinity))]] :
      List (List (Resolved.Output × String × Option Affinity))).flatten.filterMap fun (output, _) => match output with
      | .scalar expression => some expression
      | .aggregate _ => none).any (fun expression =>
        expression.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false := by
    simp [Resolved.Expr.any, Resolved.Expr.isFallibleCall]
  have ownTable : (tableScope state.catalog reference position table).ownSources =
      tableScope state.catalog reference position table := by
    simp [Scope.ownSources, tableScope, Scope.singleAt]
  have subBody := resolveQueryBody_duplicateKeys context.profile.dqsDml (tableScope state.catalog reference position table)
    (some 0) [] [] _ (some reference) value text filter term name count column columnName affinity key collation _ whereCondition
    notCall noCalls columnResolves columnGrouped columnFeeds filterResolves groupResolves ownTable
    (resolvePendingSources_table _ _ position)
  have mainResolves : ∀ shape : SubqueryShape, shape.parent = none →
      FilterResolves context.profile.dqsDml [] [] (some (.not (.exists 0))) (some (.not (.exists 0))) { later := [shape] } :=
    fun _ parentless => FilterResolves.of_term (term := .not (.exists 0)) (result := (.not (.exists 0), none))
      (by simp [namesAlias])
      (by simp [resolveOperand_not, condition, resolveOperand_exists (SubqueryShapes.find_only parentless), Bind.bind,
        Except.bind])
  have mainBody := fun shape (parentless : shape.parent = none) =>
    resolveQueryBody_simple context.profile.dqsDml [] none [shape] [] [] (Syntax.Subquery.mk [.expression (.numeric "1") none "1"]
      none [] (some (.not (.exists 0))) [] [] none none none none false none none) (simple _ _) _ (some (.not (.exists 0))) _
    (resolveColumns_one _ _ _) (by simpa [resultAliases] using mainResolves shape parentless)
    (resolvePendingSources_nil _ _) noFeed
  refine resolveStatement_select_of_resolveSelect context state
    (Syntax.Subquery.mk [.expression (.numeric "1") none "1"] none [] (some (.not (.exists 0))) [] [] none none none none false none none)
    _ rfl rfl _ ?_
  refine resolveSelect_noFrom_one_subquery context state.catalog _ _ rfl rfl rfl (by simp [starIssue]) rfl rfl rfl _ _
    (resolveSources_table state.catalog reference position table namedSource current arguments found) (by simp [starIssue]) _ _
    (by simpa [resultAliases] using subBody) _ rfl _ _ (by simpa using mainBody _ rfl) ?_
  simp [Resolved.Query.expressions, Resolved.Query.keptExpressions, Resolved.Query.simple, Resolved.Output.scalars,
    Resolved.Output.operands, Resolved.Expr.any, Resolved.Expr.isFallibleCall]

end Belay.Sqlite.Model
