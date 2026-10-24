import SuccessBalanceMissing
import SuccessBalanceSchema

/-! Success part of the corrected balance example, compiled by the surface success test. -/

set_option doc.verso true
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace BalanceExample

/-- For every database and account value, if the ledger has both needed columns, all
cents values make direct NOT BETWEEN false and the table has fewer than one million rows, SUM
returns a row. Proof sketch: resolve the account filter and cents aggregate, then bound every
integer prefix of its filtered input; retained REAL and NULL cells remain safe. -/
theorem balance_of_bounds (db : Database) (a : Value) (position cents account : Nat)
    (table : CatalogTable) (collation : Collation)
    (found : db.raw.catalog.findTable (name! "ledger") = some (position, table))
    (centsColumn : columnPosition table.columns (name! "cents") = some cents)
    (accountColumn : columnPosition table.columns (name! "account") = some account)
    (within : ∀ row ∈ Resolved.sourceRows {shape := table, rows := db.raw.rows.getD position []},
      Resolved.truthy ((Comparison.ge.apply (row[cents]?.getD .null) (.integer (-1000000000000)) collation).and
        (Comparison.le.apply (row[cents]?.getD .null) (.integer 1000000000000) collation)).not = false)
    (small : (db.raw.rows.getD position []).length < 1000000) :
    Holds (balance a) db := by
  obtain ⟨accountCell, accountAt, -⟩ := (columnPosition_eq_some_iff _ _ _).mp accountColumn
  let predicate := Resolved.Expr.compare .eq (some accountCell.affinity) (.column account) (.parameter 1) accountCell.collation
  have resolves := FilterResolves.of_term (dqs := runContext.profile.dqsDml)
    (scope := tableScope db.raw.catalog {table := name! "ledger", alias := none} position table)
    (aliases := []) (shapes := {current := none, later := []})
    (term := .compare .eq (.identifier (name! "account") .none) (.parameter 1))
    (result := (predicate, none)) (by simp [namesAlias])
    (by simp [sql_simp, accountColumn, accountAt, predicate]; rfl)
  apply (Holds.iff_selectAggregate (script := balance a) (operand := .identifier (name! "cents") .none) (alias := none) (text := "sum(cents)") (namedSource := rfl) (head := rfl)
    (reference := {table := name! "ledger", alias := none}) (build := .sum) (name := "sum")
    (resolved := .column cents) (condition := some predicate) (aggregate := .sum (.column cents))
    rfl rfl found (resolveOperand_identifier_table centsColumn) rfl (by simpa [resultAliases] using resolves) rfl
    (by simp [predicate, Resolved.Expr.calm_compare, Resolved.Expr.calm_column, Resolved.Expr.calm_parameter])
    (by simp [Resolved.Output.operands, Resolved.Expr.calm_column])).mpr
  change (sumOf (((Resolved.sourceRows {shape := table, rows := db.raw.rows.getD position []}).filter
      (fun row => Resolved.truthy (predicate.eval (Resolved.EvalContext.bound [a]) row))).map
      (fun row => row[cents]?.getD .null))).sumValue.isNone = false
  apply sumOf_no_overflow_of_between _ 1000000000000 collation (by decide)
  · intro value member
    obtain ⟨row, kept, rfl⟩ := List.mem_map.mp member
    exact within row (List.mem_filter.mp kept).1
  · have scanned : (Resolved.sourceRows {shape := table, rows := db.raw.rows.getD position []}).length =
        (db.raw.rows.getD position []).length := by
      simp only [Resolved.sourceRows, List.length_map]
      exact (Table.scanRows_perm _).length_eq
    have bounded := List.length_filter_le (fun row => Resolved.truthy (predicate.eval (Resolved.EvalContext.bound [a]) row))
      (Resolved.sourceRows {shape := table, rows := db.raw.rows.getD position []})
    simp only [List.length_map]
    omega

/-- For every database with the ledger and a table or view shadowing pragma_table_info, the guard
does not hold. Proof sketch: its resolution restriction produces an output without rows. -/
theorem shadowed_pragma (db : Database) (position : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable ledgerRef.table = some (position, table))
    (shadows : ((db.raw.catalog.findTable pragmaRef.table).isSome ||
      (db.raw.catalog.findView pragmaRef.table).isSome) = true) : ¬ Holds balanceGuard db := by
  have resolved : resolveStatement runContext db.raw.connection.resolveState balanceGuard.statements[0].1 =
      .error ⟨[8, 2, 1], .tableFunction⟩ := by
    change db.raw.connection.resolveState.withCatalog (resolveSelect runContext db.raw.catalog mainSyntax balanceQueries) = _
    rw [guard_select_shadow db.raw.catalog position table found shadows]
    rfl
  intro holds
  have output := Script.outputOn_eq_step balanceGuard db _ [] [] rfl
  change balanceGuard.outputOn db = some (match resolveStatement runContext db.raw.connection.resolveState balanceGuard.statements[0].1 with
    | .error restriction => .unmodeled restriction.reason
    | .ok (resolved, _) => resolvedStepOutput none 0 db.raw.connection [] resolved) at output
  rw [resolved] at output
  simp [Holds, output, Output.hasRows] at holds

/-- For every database with the ledger and unshadowed pragma but without cents, the guard
does not hold because resolution gives a prepare error.
Proof sketch: The missing-column preparation error contradicts the row-bearing query claim. -/
theorem missing_cents (db : Database) (position : Nat) (table : CatalogTable)
    (found : db.raw.catalog.findTable ledgerRef.table = some (position, table))
    (notTable : db.raw.catalog.findTable pragmaRef.table = none)
    (notView : db.raw.catalog.findView pragmaRef.table = none)
    (missing : columnPosition table.columns (name! "cents") = none) : ¬ Holds balanceGuard db := by
  have resolved : resolveStatement runContext db.raw.connection.resolveState balanceGuard.statements[0].1 =
      .ok (.prepareError (.expression (.noSuchColumn (name! "cents"))), db.raw.connection.resolveState) :=
    resolveStatement_select_of_resolveSelect runContext db.raw.connection.resolveState mainSyntax balanceQueries
      rfl rfl _ (guard_select_missing_cents db.raw.catalog position table found notTable notView missing)
  intro holds
  exact holds.not_fails (Fails.of_prepareError (script := balanceGuard) (isQuery := by rfl) rfl resolved)

/-- For every account value, the balance query succeeds in every complete environment on
every database with a physical ledger table where the corrected SQL guard holds.
Proof sketch: the table premise supplies the source; exclude a shadowed pragma, derive the
account column and numeric row bounds from the guard, then apply the SUM bound and
query-success bridge. -/
theorem balance_ok (a : Value) : Succeeds (balance a) (fun db =>
    (db.catalog.findTable ledgerRef.table).isSome = true ∧ Holds balanceGuard db) := by
  apply Succeeds.of_holds (query := by rfl)
  rintro db ⟨tablePresent, holds⟩
  cases found : db.raw.catalog.findTable ledgerRef.table with
  | none => simp [Belay.Sqlite.Database.catalog, found] at tablePresent
  | some pair =>
    rcases pair with ⟨position, table⟩
    cases shadows : db.raw.catalog.findTable pragmaRef.table with
    | some pair =>
      exact False.elim (shadowed_pragma db position table found (by simp [shadows]) holds)
    | none =>
      cases view : db.raw.catalog.findView pragmaRef.table with
      | some pair => exact False.elim (shadowed_pragma db position table found (by simp [view]) holds)
      | none =>
        cases column : columnPosition table.columns (name! "cents") with
        | none => exact False.elim (missing_cents db position table found shadows view column holds)
        | some index =>
          obtain ⟨cell, atIndex, -⟩ := (columnPosition_eq_some_iff _ _ _).mp column
          obtain ⟨account, accountColumn⟩ := (guard_schema db position index table cell found shadows view column atIndex holds).1
          have bounds := guard_bounds db position index table cell found shadows view column atIndex holds
          exact balance_of_bounds db a position index account table cell.collation found column accountColumn bounds.1 bounds.2

end BalanceExample
