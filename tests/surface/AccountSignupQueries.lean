import Belay

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the live-account invariant of the guide's
signup example (ADR 0017, S6). The query `SELECT 1 WHERE (SELECT count(*) FROM accounts WHERE deleted_at IS NULL
AND email = $f) <= 1` holds exactly when at most one stored row of `accounts` is live and has the email. For every
value `f` it is the guide's "at most one live account for each email". -/

set_option doc.verso true

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The signup of the guide: a new account with the email, live because the deletion time stays NULL. -/
def signupAccount (e : String) : Script := sql r"INSERT INTO accounts (email) VALUES ($e)"

/-- The invariant for one email value: at most one live account has the email. -/
def atMostOneLiveAccountWithEmail (f : Value) : Script :=
  sql r"SELECT 1 WHERE (SELECT count(*) FROM accounts WHERE deleted_at IS NULL AND email = $f) <= 1"

/-- The resolved condition {lit}`deleted_at IS NULL` of a column: the stored cell is NULL. -/
def liveCondition (cell : CatalogColumn) (position : Nat) : Resolved.Expr :=
  .compare .is (some cell.affinity) (.column position) (.literal .null) cell.collation

/-- In the scope of the table, {lit}`name IS NULL` for a column that the table has resolves to
{name}`liveCondition` of the column, without affinity. Proof sketch: unfold the resolver; the column resolves
({name}`resolveOperand_identifier_table`), NULL resolves ({name}`resolveOperand_null`), and the truth test
{lit}`IS` takes the affinity of the column. -/
theorem resolveOperand_column_is_null {dqs : Bool} (catalog : Catalog) (reference : Syntax.TableReference) (position : Nat)
    (table : CatalogTable) (name : Identifier) (index : Nat) (cell : CatalogColumn)
    (found : columnPosition table.columns name = some index) (cellAt : table.columns[index]? = some cell) :
    resolveOperand dqs (tableScope catalog reference position table) { current := some 0 } true
      (.compare .is (.identifier name .none) .null) = .ok (liveCondition cell index, none) := by
  have operand := resolveOperand_identifier_table (dqs := dqs) (shapes := { current := some 0 }) (misuse := true)
    (catalog := catalog) (reference := reference) (position := position) (quote := .none) found
  have collate := Syntax.Expr.columnCollation_identifier_table (catalog := catalog) (reference := reference)
    (position := position) (quote := .none) found
  rw [resolveOperand_arm_compare]
  simp only [operand, resolveOperand_null]
  simp [truthTest, Syntax.Expr.unquotedBoolean, liveCondition, comparisonAffinity, comparisonCollation,
    Syntax.Expr.explicitCollation, collate, cellAt,
    Except.mapError]
  rfl

/-- Over every database with a table {lit}`accounts` that has the columns {lit}`email` and {lit}`deleted_at`: at most
one live account has the email {lit}`f` exactly when the count of the rows that are live and equal to {lit}`f` in the
email is at most one. Proof sketch: apply {name}`Holds.iff_selectOne_count` to the resolved conditions; the main
condition is {name}`Resolved.truthy_count_le_one`. -/
theorem at_most_one_live_account_iff (db : Database) (f : Value) (position emailIx deletedIx : Nat)
    (table : CatalogTable) (emailCell deletedCell : CatalogColumn)
    (found : db.raw.catalog.findTable (name! "accounts") = some (position, table))
    (emailColumn : columnPosition table.columns (name! "email") = some emailIx)
    (emailAt : table.columns[emailIx]? = some emailCell)
    (deletedColumn : columnPosition table.columns (name! "deleted_at") = some deletedIx)
    (deletedAt : table.columns[deletedIx]? = some deletedCell) :
    Holds (atMostOneLiveAccountWithEmail f) db ↔
      Resolved.countMatching (Resolved.EvalContext.bound [f])
        (some (.and (liveCondition deletedCell deletedIx) (equalsParameter emailCell emailIx 1)))
        { shape := table, rows := db.raw.rows.getD position [] } ≤ 1 := by
  have mainResolves : ∀ lowest, FilterResolves runContext.profile.dqsDml [] []
      (some (.compare .le (.subquery 0) (.numeric "1")))
      (some (.compare .le none (.subquery 0) (.literal (.integer 1)) .binary)) { later := [countShape lowest] } :=
    fun lowest => FilterResolves.of_term (term := .compare .le (.subquery 0) (.numeric "1"))
      (result := (.compare .le none (.subquery 0) (.literal (.integer 1)) .binary, none)) (by simp [namesAlias]) (by
      simp [sql_simp, countShape]; rfl)
  have subResolves := FilterResolves.of_term (dqs := runContext.profile.dqsDml)
    (scope := tableScope db.raw.catalog { table := name! "accounts", alias := none } position table) (aliases := [])
    (shapes := { current := some 0 })
    (term := .and (.compare .is (.identifier (name! "deleted_at") .none) .null)
      (.compare .eq (.identifier (name! "email") .none) (.parameter 1))) (by simp [namesAlias])
    (result := (.and (liveCondition deletedCell deletedIx) (equalsParameter emailCell emailIx 1), none))
    (by
      rw [resolveOperand_and, resolveOperand_column_is_null _ _ _ _ _ _ _ deletedColumn deletedAt]
      simp [sql_simp, emailColumn, emailAt, equalsParameter, Except.mapError]
      rfl)
  refine Iff.trans (Holds.iff_selectOne_count (namedSource := rfl) (current := rfl) (head := rfl) (count := by decide)
    (arguments := rfl) found subResolves mainResolves (by simp [sql_simp]) (by simp [equalsParameter, liveCondition, sql_simp])) ?_
  rw [Resolved.truthy_count_le_one]
  simp

#print axioms at_most_one_live_account_iff

end AssertionExamples
