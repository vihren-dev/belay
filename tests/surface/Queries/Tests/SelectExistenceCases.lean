import Belay

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A04, existence and emptiness: the claims {lit}`Holds` and {lit}`Empty` of
{lit}`SELECT 1 FROM invoices WHERE amount = 0` over every database through the filter rules, with
an instance of each side on a database where it holds and on one where it does not. -/

namespace SelectExistenceCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- Some invoice has the amount 0. -/
def zeroAmount : Script := sql r"SELECT 1 FROM invoices WHERE amount = 0"

/-- The query of a zero amount has one statement. -/
theorem zeroAmount_one : zeroAmount.statements.length = 1 := rfl

/-- The resolved condition {lit}`amount = 0` over a table whose column {lit}`amount` is at
{lit}`index`, with the affinity and collation of that column. -/
def zeroCondition (table : CatalogTable) (index : Nat) : Resolved.Expr :=
  .compare .eq (comparisonAffinity (table.columns[index]?.map CatalogColumn.affinity) none) (.column index)
    (.literal (.integer 0)) ((table.columns[index]?.map (·.collation)).getD .binary)

/-- For every database whose catalog has a table {lit}`invoices` at a position with a column
{lit}`amount` at {lit}`index`, and every property {lit}`Q` of a result: the query of a zero amount
returns a result with {lit}`Q` exactly when every result that the model permits over the scan of the
table, with the condition {name}`zeroCondition`, has {lit}`Q`. Proof sketch:
{name}`resolveStatement_select_one_from` resolves the query, and
{name}`Run.query_returnsResult_calmTable` reads its results. -/
theorem zeroAmount_results (db : Database) {position index : Nat} {table : CatalogTable}
    (found : db.raw.catalog.findTable (name! "invoices") = some (position, table))
    (column : columnPosition table.columns (name! "amount") = some index) (property : List (List Value) → Prop) :
    (db.run zeroAmount).returnsResult property ↔
      ∀ result ∈ (Resolved.Query.simple [.first position] (some (zeroCondition table index))
        [.scalar (.literal (.integer 1))] ["1"]).possibleResults (Resolved.EvalContext.bound [])
          (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] }), property result := by
  have resolves := FilterResolves.of_term (dqs := runContext.profile.dqsDml)
    (scope := tableScope db.raw.catalog { table := name! "invoices", alias := none } position table) (aliases := [])
    (shapes := { later := [] }) (term := .compare .eq (.identifier (name! "amount") .none) (.numeric "0"))
    (result := (zeroCondition table index, none)) (by simp [namesAlias]) (by simp [sql_simp, column]; rfl)
  have resolved := resolveStatement_select_one_from runContext (db.raw.connection Env.default.counters).resolveState
    { table := name! "invoices", alias := none } _ position table _ rfl rfl rfl found resolves
  rw [Run.send_returnsResult_iff_query (script := zeroAmount) zeroAmount_one]
  exact Run.query_returnsResult_calmTable (script := zeroAmount) rfl zeroAmount_one db Env.default resolved rfl
    (Database.table_of_findTable _ _ _ _ found)
    (Resolved.Statement.Calm.selectOne position _ (by simp [zeroCondition, sql_simp])) rfl rfl rfl
    (by simp [Resolved.Query.fails, Resolved.Query.simple]) rfl property

/-- A04, existence and emptiness: for every database as in {name}`zeroAmount_results`,

* {lit}`Holds` of the query of a zero amount holds exactly when {name}`zeroCondition` is true for
  some row of the scan of the table,
* {lit}`Empty` of it holds exactly when the condition is not true for any row of the scan, and
* {lit}`Fails` of it does not hold.

Proof sketch: {name}`zeroAmount_results` with the plain existence and emptiness rules
({name}`Resolved.Query.forall_possibleResults_ne_nil_plain`,
{name}`Resolved.Query.forall_possibleResults_eq_nil_plain`); one of the two claims holds, and
neither allows an error ({name}`Holds.not_fails`, {name}`Empty.not_fails`). -/
theorem zeroAmount_claims (db : Database) {position index : Nat} {table : CatalogTable}
    (found : db.raw.catalog.findTable (name! "invoices") = some (position, table))
    (column : columnPosition table.columns (name! "amount") = some index) :
    (Holds zeroAmount db ↔ ∃ row ∈ Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] },
      Resolved.truthy ((zeroCondition table index).eval (Resolved.EvalContext.bound []) row) = true) ∧
    (Belay.Sqlite.Empty zeroAmount db ↔ ∀ row ∈ Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] },
      Resolved.truthy ((zeroCondition table index).eval (Resolved.EvalContext.bound []) row) = false) ∧
    ¬ Fails zeroAmount db := by
  have holds : Holds zeroAmount db ↔ _ := (zeroAmount_results db found column _).trans
    (Resolved.Query.forall_possibleResults_ne_nil_plain rfl rfl rfl rfl rfl)
  have empty : Belay.Sqlite.Empty zeroAmount db ↔ _ := (zeroAmount_results db found column _).trans
    (Resolved.Query.forall_possibleResults_eq_nil_plain rfl rfl rfl rfl rfl)
  simp only [Resolved.Query.simple, Option.all_some] at holds empty
  refine ⟨holds, empty, fun fails => ?_⟩
  by_cases kept : ∃ row ∈ Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] },
      Resolved.truthy ((zeroCondition table index).eval (Resolved.EvalContext.bound []) row) = true
  · exact Holds.not_fails (holds.mpr kept) fails
  · exact Empty.not_fails (empty.mpr fun row member => by simpa using fun same => kept ⟨row, member, same⟩) fails

/-- The guide's first database: table {lit}`invoices` with two open invoices, of 10 and of 0. -/
def shop : Database := db! r"
  CREATE TABLE invoices (
    id INTEGER PRIMARY KEY,
    customer TEXT NOT NULL,
    amount INTEGER NOT NULL CHECK (amount >= 0),
    status TEXT NOT NULL DEFAULT 'open'
  );
  INSERT INTO invoices (id, customer, amount) VALUES (1, 'acme', 10), (2, 'zeta', 0);"

/-- A table with an amount column and no zero amount. -/
def positiveOnly : Database := db! r"CREATE TABLE invoices (amount INTEGER); INSERT INTO invoices VALUES (1);"

/-- Instances of both sides: on {name}`shop`, which has a zero amount, {lit}`Holds` holds and
{lit}`Empty` does not; on {name}`positiveOnly`, {lit}`Empty` holds and {lit}`Holds` does not; on
both, {lit}`Fails` does not hold. The premises of {name}`zeroAmount_claims` hold on both, so the
claims are not vacuous there. -/
theorem zeroAmount_instances :
    Holds zeroAmount shop ∧ ¬ Belay.Sqlite.Empty zeroAmount shop ∧ ¬ Fails zeroAmount shop ∧
      Belay.Sqlite.Empty zeroAmount positiveOnly ∧ ¬ Holds zeroAmount positiveOnly ∧
      ¬ Fails zeroAmount positiveOnly ∧
      (shop.raw.catalog.findTable (name! "invoices")).any
        (fun entry => (columnPosition entry.2.columns (name! "amount")).isSome) ∧
      (positiveOnly.raw.catalog.findTable (name! "invoices")).any
        (fun entry => (columnPosition entry.2.columns (name! "amount")).isSome) := by
  decide +kernel

#print axioms zeroAmount_results
#print axioms zeroAmount_claims
#print axioms zeroAmount_instances

end SelectExistenceCases
