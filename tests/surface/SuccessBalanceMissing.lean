import SuccessBalanceSchema

/-! Missing part of the corrected balance example, compiled by the surface success test. -/

set_option doc.verso true
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace BalanceExample

/-- For every catalog without a ledger table, the first guard subquery reports that
missing table. Proof sketch: the first source lookup fails before later subqueries are visited. -/
theorem guard_scopes_missing (catalog : Catalog)
    (missing : catalog.findTable ledgerRef.table = none) :
    subqueryScopes catalog 8 (around [] []) none balanceQueries = .error (.noSuchTable ledgerRef.table) := by
  have order : scopeOrder none balanceQueries 5 none = [0, 1, 2, 3] := rfl
  have application : reservedName ledgerRef.table = false := by decide
  have noFunction : eponymousName ledgerRef.table = false := by decide
  unfold subqueryScopes
  rw [show balanceQueries.length + 1 = 5 from rfl, order]
  simp only [ledgerRef] at missing application noFunction
  simp [balanceQueries, oneQuery, countSyntax, compoundOf, subqueryScope, QueryScope.sourceIndexes,
    around, Scope.columns, resolveSources, resolveReference, ledgerRef, resolveTableReference,
    missing, application, noFunction, maximumJoinTables, SourceIssue.under,
    Bind.bind, Except.bind, Except.mapError, Functor.map, Except.map, Pure.pure, Except.pure]

/-- For every catalog without a ledger table, guard resolution gives its prepare error
and preserves the catalog.
Proof sketch: Lift the first subquery source error through complete query resolution. -/
theorem guard_select_missing (catalog : Catalog)
    (missing : catalog.findTable ledgerRef.table = none) :
    resolveSelect runContext catalog mainSyntax balanceQueries =
      .ok (.prepareError (.noSuchTable ledgerRef.table), catalog) := by
  have scopes := guard_scopes_missing catalog missing
  dsimp only [around] at scopes
  have noMain : ∀ queries prefix_, resolveSources catalog none [] 0 queries prefix_ = .ok ([], []) := by intros; rfl
  unfold resolveSelect
  simp [mainSyntax, noMain, starIssue, resultAliases, scopes, prepareError,
    Bind.bind, Except.bind, Except.mapError, Functor.map, Except.map, Pure.pure, Except.pure]

/-- For every catalog with both the ledger and a table named pragma_table_info, the
metadata source is a restricted table-function call.
Proof sketch: the ledger sources resolve, then the first metadata source finds the shadowing table. -/
theorem guard_scopes_shadow (catalog : Catalog) (position shadow : Nat) (table other : CatalogTable)
    (found : catalog.findTable ledgerRef.table = some (position, table))
    (shadows : catalog.findTable pragmaRef.table = some (shadow, other)) :
    subqueryScopes catalog 8 (around [] []) none balanceQueries =
      .error (.value (.restriction [8, 2, 1] .tableFunction)) := by
  have sources := fun queries prefix_ => resolveSources_table catalog ledgerRef position table rfl rfl found queries prefix_
  have order : scopeOrder none balanceQueries 5 none = [0, 1, 2, 3] := rfl
  have refused : ∀ queries prefix_, resolveSources catalog (some pragmaRef) [] 0 queries prefix_ =
      .error (.value (.restriction (prefix_ ++ [1]) .tableFunction)) := by
    intro queries prefix_
    have prefixed : (bytes! "pragma_").isPrefixOf pragmaRef.table.folded = true := by decide
    simp only [pragmaRef] at shadows prefixed
    simp [resolveSources, resolveReference, pragmaRef, pragmaReference, shadows, prefixed,
      maximumJoinTables, SourceIssue.under, ValueIssue.under,
      Bind.bind, Except.bind, Except.mapError, Functor.map, Except.map, Pure.pure, Except.pure]
  unfold subqueryScopes
  rw [show balanceQueries.length + 1 = 5 from rfl, order]
  simp [balanceQueries, oneQuery, countSyntax, compoundOf, subqueryScope, QueryScope.sourceIndexes,
    around, Scope.columns, sources, Scope.enclose, starIssue, resultAliases, refused,
    Bind.bind, Except.bind, Except.mapError, Functor.map, Except.map, Pure.pure, Except.pure]

/-- For every catalog with the ledger and a table shadowing pragma_table_info, the
complete guard reports the table-function restriction at the first metadata source.
Proof sketch: Lift the first metadata source restriction through complete query resolution. -/
theorem guard_select_shadow (catalog : Catalog) (position shadow : Nat) (table other : CatalogTable)
    (found : catalog.findTable ledgerRef.table = some (position, table))
    (shadows : catalog.findTable pragmaRef.table = some (shadow, other)) :
    resolveSelect runContext catalog mainSyntax balanceQueries = .error ⟨[8, 2, 1], .tableFunction⟩ := by
  have scopes := guard_scopes_shadow catalog position shadow table other found shadows
  dsimp only [around] at scopes
  have noMain : ∀ queries prefix_, resolveSources catalog none [] 0 queries prefix_ = .ok ([], []) := by intros; rfl
  unfold resolveSelect
  simp [mainSyntax, noMain, starIssue, resultAliases, scopes, issueResolution, restrict,
    Bind.bind, Except.bind, Except.mapError, Functor.map, Except.map, Pure.pure, Except.pure]

/-- For every table without cents and every subquery shape, the range body reports a
missing-column prepare error. The unquoted identifier is neither a rowid nor a Boolean keyword.
Proof sketch: Resolve the cents identifier as missing and propagate its preparation error. -/
theorem range_body_missing (catalog : Catalog) (position : Nat) (table : CatalogTable)
    (current : Option Nat) (later : List SubqueryShape)
    (missing : columnPosition table.columns (name! "cents") = none) :
    resolveQueryBody true (tableScope catalog ledgerRef position table) {current, later} [] (tablePending position)
      (oneQuery ledgerRef (some rangeSyntax)) = .error (.prepare (.noSuchColumn (name! "cents"))) := by
  have absent : (tableScope catalog ledgerRef position table).resolveName (name! "cents") = .missing := by
    simp [tableScope, Scope.resolveName, Scope.depths, Scope.single, Scope.resolveAt, Scope.resolveStep, missing]
  have one : queryNumeric "1" false = .ok (.integer 1) := rfl
  have noRowid : rowidName (name! "cents") = false := by decide
  have noBool : booleanKeywordName (name! "cents") = false := by decide
  simp [noRowid, noBool, Model.condition, resolveQueryBody, oneQuery, resolveAll, resolveAllFrom, Syntax.Expr.aggregateCalls, aggregateCall,
    Syntax.Expr.distinctList, resolveResultColumn, resolveOperand, rangeSyntax, absent, one,
    resultAliases, resultCollations, namesAlias, Syntax.Expr.collationIn, definedName,
    ValueIssue.under, Bind.bind, Except.bind, Except.mapError, Functor.map, Except.map, Pure.pure, Except.pure]

/-- For every table without cents, resolution of the four guard bodies fails in the
first range body. Proof sketch: the first body fails before its result shape or later bodies is used. -/
theorem guard_bodies_missing (catalog : Catalog) (position : Nat) (table : CatalogTable)
    (missing : columnPosition table.columns (name! "cents") = none) :
    resolveSubqueryBodies true catalog 8 (around [] []) none
      [ledgerScope catalog position table, ledgerScope catalog position table,
        pragmaScope table.infoRows, pragmaScope table.infoRows] balanceQueries =
      .error (.prepare (.noSuchColumn (name! "cents"))) := by
  let scopes := [ledgerScope catalog position table, ledgerScope catalog position table,
        pragmaScope table.infoRows, pragmaScope table.infoRows]
  have order : subqueryBodyOrder (around [] []) none scopes balanceQueries 5 none = [0, 1, 2, 3] := by
    simp [subqueryBodyOrder, scopes, balanceQueries, oneQuery, countSyntax, compoundOf,
      QueryScope.sourceIndexes, around]
    rfl
  have failed := fun current later => range_body_missing catalog position table current later missing
  dsimp only [oneQuery] at failed
  have rangeFour : List.range 4 = [0, 1, 2, 3] := rfl
  unfold resolveSubqueryBodies
  rw [show balanceQueries.length + 1 = 5 from rfl, order]
  simp [rangeFour, balanceQueries, oneQuery, countSyntax, QueryScope.refresh, Scope.refreshSources,
    ledgerScope, pragmaScope, around, failed, ValueIssue.under,
    Bind.bind, Except.bind, Except.mapError, Functor.map, Except.map, Pure.pure, Except.pure]

/-- For every catalog with the ledger and unshadowed pragma but without cents, the
guard resolves to the missing-column prepare error and preserves the catalog.
Proof sketch: Resolve the existing sources, then propagate the first body error. -/
theorem guard_select_missing_cents (catalog : Catalog) (position : Nat) (table : CatalogTable)
    (found : catalog.findTable ledgerRef.table = some (position, table))
    (notTable : catalog.findTable pragmaRef.table = none)
    (missing : columnPosition table.columns (name! "cents") = none) :
    resolveSelect runContext catalog mainSyntax balanceQueries =
      .ok (.prepareError (.expression (.noSuchColumn (name! "cents"))), catalog) := by
  have scopes := guard_scopes catalog position table found notTable
  have bodies := guard_bodies_missing catalog position table missing
  dsimp only [around] at scopes bodies
  have dqs : runContext.profile.dqsDml = true := rfl
  have noMain : ∀ queries prefix_, resolveSources catalog none [] 0 queries prefix_ = .ok ([], []) := by intros; rfl
  unfold resolveSelect
  simp [mainSyntax, noMain, starIssue, resultAliases, scopes, bodies, dqs, issueResolution, prepareError,
    Bind.bind, Except.bind, Except.mapError, Functor.map, Except.map, Pure.pure, Except.pure]

end BalanceExample
