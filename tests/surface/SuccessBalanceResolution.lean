import SuccessBalanceSyntax

/-! Resolution part of the corrected balance example, compiled by the surface success test. -/

set_option doc.verso true
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace BalanceExample

/-- For every metadata row list, target name and subquery shape, the name predicate resolves
to the exact byte comparison.
Proof sketch: Resolve the metadata name field, then the literal comparison. -/
theorem name_resolves (rows : List (List Value)) (name : List UInt8) (current : Option Nat) (later : List SubqueryShape) :
    FilterResolves true (tableInfoScope pragmaRef (bytes! "ledger") rows) []
      (some (nameSyntax name)) (some (nameResolved name)) {current, later} := by
  apply FilterResolves.of_term (result := (nameResolved name, none))
  · simp [nameSyntax, namesAlias]
  · simp [sql_simp, nameSyntax, nameResolved]
    rfl

/-- For every metadata row list and subquery shape, the cents/type predicate resolves
to the two field comparisons.
Proof sketch: Resolve both metadata fields and combine their comparisons with AND. -/
theorem typed_resolves (rows : List (List Value)) (current : Option Nat) (later : List SubqueryShape) :
    FilterResolves true (tableInfoScope pragmaRef (bytes! "ledger") rows) []
      (some typedSyntax) (some typedResolved) {current, later} := by
  apply FilterResolves.of_term (result := (typedResolved, none))
  · simp [typedSyntax, typeSyntax, nameSyntax, namesAlias]
  · simp [sql_simp, typedSyntax, typedResolved, typeSyntax, nameSyntax, nameResolved,
      resolveOperand_tableInfo_type, tableInfoScope_resolveName_type, tableInfoScope_collation_type]
    rfl

/-- For every scope and one-source SELECT 1 body whose filter and pending sources resolve,
the body resolves to that simple query. The result follows from the shared simple-body law.
Proof sketch: Apply the shared simple-body equation to the given filter and sources. -/
theorem one_body (scope : Scope) (current : Option Nat) (later : List SubqueryShape)
    (source : Syntax.TableReference) (filter : Option Syntax.Expr)
    (resolved : Option Resolved.Expr) (pending : List PendingSource) (sources : List Resolved.QuerySource)
    (filterOk : FilterResolves true scope [] filter resolved {current, later})
    (pendingOk : resolvePendingSources true scope pending = .ok sources) :
    resolveQueryBody true scope {current, later} [] pending (oneQuery source filter) =
      .ok (Resolved.Query.simple sources resolved [.scalar (.literal (.integer 1))] ["1"], none) := by
  exact resolveQueryBody_simple true scope current later [] pending (oneQuery source filter)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ _ resolved sources
    (resolveColumns_one _ _ _) (by simpa [oneQuery, resultAliases] using filterOk) pendingOk rfl

/-- For every catalog with a ledger table and no table or view shadowing the pragma, all four
subquery scopes are the two ledger scopes and two metadata scopes.
Proof sketch: apply the named-source laws at each sibling diagnostic prefix. -/
theorem guard_scopes (catalog : Catalog) (position : Nat) (table : CatalogTable)
    (found : catalog.findTable ledgerRef.table = some (position, table))
    (notTable : catalog.findTable pragmaRef.table = none)
    (notView : catalog.findView pragmaRef.table = none) :
    subqueryScopes catalog 8 (around [] []) none balanceQueries = .ok
      [ledgerScope catalog position table, ledgerScope catalog position table,
        pragmaScope table.infoRows, pragmaScope table.infoRows] := by
  have sources := fun queries prefix_ => resolveSources_table catalog ledgerRef position table rfl rfl rfl found queries prefix_
  have info := Catalog.tableInfoRows_of_findTable catalog ledgerRef.table position table found
  have metadata := fun queries prefix_ => resolveSources_tableInfo catalog pragmaRef (bytes! "ledger") table.infoRows rfl rfl rfl (by decide) notTable notView info queries prefix_
  have order : scopeOrder none balanceQueries 5 none = [0, 1, 2, 3] := rfl
  unfold subqueryScopes
  rw [show balanceQueries.length + 1 = 5 from rfl, order]
  simp [balanceQueries, oneQuery, countSyntax, compoundOf,
    subqueryScope, QueryScope.sourceIndexes, around, Scope.columns, sources, metadata,
    Scope.enclose, starIssue, resultAliases, ledgerScope, pragmaScope, tablePending, pragmaPending,
    Bind.bind, Except.bind, Except.mapError, Functor.map, Except.map, Pure.pure, Except.pure]
  rfl

/-- For every catalog with a physical ledger table, this guard needs no query-source
copies. Its metadata sources have arguments, so even a shadowing view is checked by
ordinary function resolution. Proof sketch: table lookup excludes a ledger view;
all other references are calls rather than expandable view sources. -/
theorem guard_no_copies (catalog : Catalog) (position : Nat) (table : CatalogTable)
    (found : catalog.findTable ledgerRef.table = some (position, table)) :
    querySourceCopiesNeeded catalog mainSyntax balanceQueries = false := by
  have notView : catalog.findView (name! "ledger") = none := Catalog.findView_none_of_table found
  simp [querySourceCopiesNeeded, Syntax.TableReference.namesStoredView, mainSyntax, balanceQueries, oneQuery, countSyntax,
    ledgerRef, pragmaRef, notView]

/-- For every existing cents column and subquery shape, the range body resolves with
the column affinity and collation. Resolve the condition and use the simple-body law.
Proof sketch: Resolve the cents comparisons with column affinity, then apply the SELECT 1 body law. -/
theorem range_body (catalog : Catalog) (position index : Nat) (table : CatalogTable) (cell : CatalogColumn)
    (current : Option Nat) (later : List SubqueryShape)
    (column : columnPosition table.columns (name! "cents") = some index)
    (atIndex : table.columns[index]? = some cell) :
    resolveQueryBody true (tableScope catalog ledgerRef position table) {current, later} [] (tablePending position)
      (oneQuery ledgerRef (some rangeSyntax)) = .ok (rangeQuery position index cell, none) := by
  apply one_body
  · apply FilterResolves.of_term (result := (rangeResolved index cell, none))
    · simp [rangeSyntax, namesAlias]
    · simp [sql_simp, rangeSyntax, rangeResolved, column, atIndex]
      rfl
  · exact resolvePendingSources_table _ _ _

end BalanceExample
