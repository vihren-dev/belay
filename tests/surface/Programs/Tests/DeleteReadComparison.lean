import SelectContextCases

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

namespace DeleteReadComparison
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectContextCases (bigScript deleteScript bigAt big_eq)
open SelectGroupCases (cell)
open SelectJoinCases (shop ordersShape shop_found)
open SelectDerivedCases (Big bigCondition)

/-- The equivalent read on the starting database. -/
def referenceScript : Script := sql r"SELECT customer_id, amount FROM orders WHERE customer_id IS NOT NULL AND amount > 5"

/-- A successful query returns the expected rows up to order, including duplicates. -/
def returnsBag (expected : List (List Value)) (result : Except Nat (List (List Value))) : Prop :=
  match result with
  | .ok rows => rows.Perm expected
  | .error _ => False

/-- The qualifying orders that have a customer in the starting database. -/
def expected (database : Model.Database) : List (List Value) :=
  ((Resolved.sourceRows { shape := ordersShape, rows := database.rows.getD 1 [] }).filter
    (fun row => !(cell 1 row).isNull && Big row)).map (fun row => [cell 1 row, cell 2 row])

/-- The reference SELECT returns the qualifying rows from its starting database. -/
theorem reference_at (state : ExecutionContext) (schema : state.HasCatalog shop) :
    (query referenceScript rfl).check (fun result _ => returnsBag (expected state.connection.state.database) result) state := by
  sql_select [schema, returnsBag, expected, big_eq, bigCondition, Resolved.truthy_and, Resolved.Expr.eval_and]

/-- The amount filter reads the qualifying orders visible to the connection. -/
theorem big_start (state : ExecutionContext) (schema : state.HasCatalog shop) :
    (query bigScript rfl).check (fun result _ => returnsBag (bigAt state.connection.state.database) result) state := by
  sql_select [schema, returnsBag, bigAt, big_eq, bigCondition]

/-- The resolved filter that removes orders without a customer. -/
private def nullFilter : Option Resolved.Expr :=
  some (.compare .is (some .integer) (.column 1) (.literal .null) .binary)

/-- An order survives the DELETE exactly when its customer cell is non-NULL. -/
private theorem keeps_customer (ctx : Resolved.EvalContext) (row : List Value) :
    (!Resolved.conditionKeeps nullFilter ctx row) = !(cell 1 row).isNull := by
  exact (Resolved.truthy_isNot ..).symm.trans (Resolved.truthy_isNot_null (some .integer) .binary (cell 1 row))

/-- Check {name}`Resolved.truthy_isNot` on a non-NULL operand. For every order, including one
with a NULL customer, {lit}`customer_id IS NOT 7` keeps it exactly when {lit}`customer_id IS 7`
would spare it in a DELETE. -/
theorem survives_delete_customer_seven (ctx : Resolved.EvalContext) (row : List Value) :
    let condition := fun op => some (Resolved.Expr.compare op (some .integer) (.column 1) (.literal (.integer 7)) .binary)
    Resolved.conditionKeeps (condition .isNot) ctx row = !Resolved.conditionKeeps (condition .is) ctx row := by
  exact Resolved.truthy_isNot _ _ _

/-- The surviving big orders equal the original big orders with non-NULL customer cells, up to order. -/
private theorem after_delete_rows (db : Database) (schema : db.HasCatalog shop)
    (ctx : Resolved.EvalContext) :
    let table : Table := ⟨ordersShape, db.raw.rows.getD 1 []⟩
    (bigAt (db.raw.setRows 1 (LiteralData.deleted ctx table nullFilter).rows)).Perm (expected db.raw) := by
  let table : Table := ⟨ordersShape, db.raw.rows.getD 1 []⟩
  have aligned := Model.Database.position_lt_rows db.valid.admitted.rowsShaped (shop_found db schema).2
  dsimp only
  unfold bigAt expected
  rw [Model.Database.rows_getD_setRows _ aligned]
  apply List.Perm.map
  simpa only [List.filter_filter, keeps_customer, Bool.and_comm, table, LiteralData.deleted] using
    (Resolved.sourceRows_deleted table ctx nullFilter).filter Big

/-- The DELETE preserves the catalog and leaves exactly the expected big orders. -/
theorem delete_effect (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (send deleteScript).check (fun _ final =>
      final.HasCatalog shop ∧ (bigAt final.connection.state.database).Perm (expected db.raw))
      (ExecutionContext.initial db env) := by
  sql_run [schema]
  exact ⟨schema, after_delete_rows db schema _⟩

/-- Both programs succeed and return the same rows up to permutation for every database with the shop catalog. Proof sketch: the write preserves the catalog and the surviving big orders match the reference filter. -/
theorem delete_then_select_eq_filtered_select (db : Database) (env : Env)
    (schema : db.HasCatalog shop) :
    let start := ExecutionContext.initial db env
    ∃ rows,
      (do let _ ← send deleteScript; query bigScript rfl).check
        (fun result _ => returnsBag rows result) start ∧
      (query referenceScript rfl).check (fun result _ => returnsBag rows result) start := by
  refine ⟨expected db.raw, ?_, reference_at _ schema⟩
  apply (Sql.check_bind _ _ _ _).2
  refine Sql.check_mono (delete_effect db env schema) fun _ final ⟨catalog, same⟩ => ?_
  refine Sql.check_mono (big_start final catalog) fun result _ h => ?_
  cases result with
  | error _ => exact False.elim h
  | ok rows => exact List.Perm.trans h same

#print axioms survives_delete_customer_seven
#print axioms delete_then_select_eq_filtered_select

end DeleteReadComparison
