import SuccessBalanceResolution

/-! ResolveGuard part of the corrected balance example, compiled by the surface success test. -/

set_option doc.verso true
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace BalanceExample

/-- For every table with a cents column, the four bodies resolve to the guard queries
and their result shapes in the given scopes.
Proof sketch: resolve the range and metadata conditions, then compose the independent bodies. -/
theorem guard_bodies (catalog : Catalog) (position index : Nat) (table : CatalogTable) (cell : CatalogColumn)
    (column : columnPosition table.columns (name! "cents") = some index)
    (atIndex : table.columns[index]? = some cell) :
    resolveSubqueryBodies true catalog 8 (around [] []) none
      [ledgerScope catalog position table, ledgerScope catalog position table,
        pragmaScope table.infoRows, pragmaScope table.infoRows] balanceQueries =
      .ok (guardQueries position index table cell, guardShapes index) := by
  let scopes := [ledgerScope catalog position table, ledgerScope catalog position table,
        pragmaScope table.infoRows, pragmaScope table.infoRows]
  have order : subqueryBodyOrder (around [] []) none scopes balanceQueries 5 none = [0, 1, 2, 3] := by
    simp [subqueryBodyOrder, scopes, balanceQueries, oneQuery, countSyntax, compoundOf,
      QueryScope.sourceIndexes, around]
    rfl
  have rangeOk := fun current later => range_body catalog position index table cell current later column atIndex
  have countOk := fun current later => resolveQueryBody_count true (tableScope catalog ledgerRef position table)
    current later [] (tablePending position) (some ledgerRef) none "count" none "count(*)" rfl none
    [Resolved.QuerySource.first position] (Or.inl ⟨rfl, rfl⟩) (resolvePendingSources_table _ _ _)
  have accountOk := fun current later => one_body (tableInfoScope pragmaRef (bytes! "ledger") table.infoRows)
    current later pragmaRef (some (nameSyntax (bytes! "account"))) (some (nameResolved (bytes! "account")))
    (pragmaPending table.infoRows) _ (name_resolves _ _ _ _) (resolvePendingSources_pragma _ _ _)
  have typeOk := fun current later => one_body (tableInfoScope pragmaRef (bytes! "ledger") table.infoRows)
    current later pragmaRef (some typedSyntax) (some typedResolved)
    (pragmaPending table.infoRows) _ (typed_resolves _ _ _) (resolvePendingSources_pragma _ _ _)
  have rangeFour : List.range 4 = [0, 1, 2, 3] := rfl
  dsimp only [oneQuery] at rangeOk accountOk typeOk
  unfold resolveSubqueryBodies
  rw [show balanceQueries.length + 1 = 5 from rfl, order]
  simp [rangeFour, List.lookup, subqueryShape, balanceQueries, oneQuery, countSyntax, QueryScope.refresh, Scope.refreshSources, QueryScope.sourceIndexes, compoundColumnsIssue, compoundOf,
    ledgerScope, pragmaScope, around, rangeOk, column, atIndex, countOk, accountOk, typeOk,
    Bind.bind, Except.bind, Except.mapError, Functor.map, Except.map, Pure.pure, Except.pure]
  simp [guardQueries, guardShapes, rangeShape, balanceCountShape, rangeQuery, metadataQuery,
    Resolved.Query.simple, Resolved.Query.countOf, Resolved.QuerySource.first, Resolved.QuerySource.pragma,
    firstCollations, Syntax.Expr.explicitCollation, Syntax.Expr.columnCollation,
    Resolved.Query.expressions, Resolved.QuerySource.expressions, Resolved.Query.keptExpressions,
    Resolved.Output.scalars, Resolved.Output.operands, Resolved.Expr.lowestRead,
    rangeResolved, nameResolved, typedResolved, minPosition]

/-- For every cents position, the outer filter resolves to the four-subquery conjunction.
Proof sketch: Resolve the four indexed subquery references and their conjunction. -/
theorem main_filter (index : Nat) :
    FilterResolves true [] [] (some guardSyntax) (some guardCondition) {later := guardShapes index} := by
  apply FilterResolves.of_term (result := (guardCondition, none))
  · simp [guardSyntax, namesAlias]
  · simp [sql_simp, guardSyntax, guardCondition, guardShapes, rangeShape, balanceCountShape,
      SubqueryShapes.find, SubqueryShapes.base, SubqueryShapes.column]
    rfl

/-- For every cents position, the outer SELECT 1 body resolves to the guard condition.
Proof sketch: Apply the simple-body law to the resolved outer filter and empty source list. -/
theorem main_body (index : Nat) :
    resolveQueryBody true [] {later := guardShapes index} [] [] mainSyntax =
      .ok (Resolved.Query.selectOneWhere guardCondition, none) := by
  exact resolveQueryBody_simple true [] none (guardShapes index) [] [] mainSyntax
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ _ (some guardCondition) []
    (resolveColumns_one _ _ _) (by simpa [mainSyntax, resultAliases] using main_filter index)
    (resolvePendingSources_nil _ _) rfl

/-- For every catalog with a ledger table, an existing cents column and an unshadowed
pragma, the complete guard resolves to its query and leaves the catalog unchanged.
Proof sketch: compose source scopes, subquery bodies and the outer body. -/
theorem guard_select (catalog : Catalog) (position index : Nat) (table : CatalogTable) (cell : CatalogColumn)
    (found : catalog.findTable ledgerRef.table = some (position, table))
    (notTable : catalog.findTable pragmaRef.table = none)
    (column : columnPosition table.columns (name! "cents") = some index)
    (atIndex : table.columns[index]? = some cell) :
    resolveSelect runContext catalog mainSyntax balanceQueries =
      .ok (.query (Resolved.Query.selectOneWhere guardCondition) (guardQueries position index table cell), catalog) := by
  have scopes := guard_scopes catalog position table found notTable
  have bodies := guard_bodies catalog position index table cell column atIndex
  have main := main_body index
  have dqs : runContext.profile.dqsDml = true := rfl
  have noMain : ∀ queries prefix_, resolveSources catalog none [] 0 queries prefix_ = .ok ([], []) := by intros; rfl
  dsimp only [around] at scopes bodies
  dsimp only [mainSyntax, guardShapes, rangeShape, balanceCountShape] at main
  have ordinary : balanceQueries.any (·.commonTable.isSome) = false := rfl
  unfold resolveSelect
  simp only [prepareCommonTables, ordinary, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp only [mainSyntax, noMain]
  simp [CommonTableCopies.recursionIssue, dqs, scopes, bodies, main, around, mainSyntax, starIssue, resultAliases,
    QueryScope.refresh, Scope.refreshSources, guardShapes, rangeShape, balanceCountShape,
    Bind.bind, Except.bind, Except.mapError, Functor.map, Except.map, Pure.pure, Except.pure]

  simp [Resolved.Query.selectOneWhere, Resolved.Query.simple, Resolved.Query.expressions,
    Resolved.Query.keptExpressions, Resolved.Output.scalars, Resolved.Output.operands,
    guardCondition, Resolved.Expr.any, Resolved.Expr.isFallibleCall]

end BalanceExample
