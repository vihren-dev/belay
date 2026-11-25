import SelectDerivedSupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! ADR 0027 case A21 uses {name}`Belay.Sqlite.Sql.check_query_of_step_rows` to read orders at
the connection reached by a write. -/

namespace SelectContextCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases (cell)
open SelectJoinCases (shop ordersShape shop_found shop_state partial_)
open SelectDerivedCases (bigCondition bigQuery Big)

/-- The A21 query, which resolves to {name}`bigQuery`. -/
def bigScript : Script := sql r"SELECT customer_id, amount FROM orders WHERE amount > 5"

/-- The specification of {name}`bigQuery` over a database of the model: the {lit}`customer_id`
and the {lit}`amount` of each {name}`Big` row of {lit}`orders` at position 1, in scan order. -/
def bigAt (database : Model.Database) : List (List Value) :=
  ((Resolved.sourceRows { shape := ordersShape, rows := database.rows.getD 1 [] }).filter Big).map
    fun order => [cell 1 order, cell 2 order]

/-- The A21 post of a result and a reached context: the result is successful and a permutation
of {name}`bigAt` of the database of the reached context. An error does not satisfy it. -/
def ReadsBig (result : Except Nat (List (List Value))) (final : ExecutionContext) : Prop :=
  match result with
  | .ok rows => rows.Perm (bigAt final.connection.state.database)
  | .error _ => False

/-- {name}`Big` is the function that gives, for each row, the truth of {name}`bigCondition` on it. The simplifier
unfolds a definition only where it is applied, and {name}`bigAt` uses {name}`Big` as the argument of a
filter; with this hint, {lit}`sql_select` unfolds it there. -/
theorem big_eq : Big = fun order => Resolved.truthy (bigCondition.eval (Resolved.EvalContext.bound []) order) := rfl

/-- At any context with the catalog of {name}`shop`, the query returns a permutation of the
qualifying rows visible in that context, as specified by {name}`ReadsBig`. -/
theorem big_at (state : ExecutionContext) (schema : state.HasCatalog shop) :
    (query bigScript rfl).check ReadsBig state := by
  sql_select [schema, ReadsBig, bigAt, big_eq, bigCondition]

/-- If every context reached by the first program has the catalog of {name}`shop`, the
following query reads the qualifying orders there. Proof sketch: apply {name}`big_at` after the bind. -/
theorem big_after {α : Type} (first : Sql α) (state : ExecutionContext)
    (reaches : first.check (fun _ final => final.HasCatalog shop) state) :
    (do let _ ← first; query bigScript rfl).check ReadsBig state := by
  refine (Sql.check_bind _ _ _ _).2 (Sql.check_mono reaches fun _ final shape => ?_)
  exact big_at final shape

/-- The A21 write, which deletes the orders without a customer. -/
def deleteScript : Script := sql r"DELETE FROM orders WHERE customer_id IS NULL"

/-- A21, a write and a following SELECT: for every database with the catalog of {name}`shop`
and environment, if the model runs the statement of {name}`deleteScript` on the connection of
the environment to a step that continues, then the program that sends {name}`deleteScript` and
then runs {name}`bigScript` checks {name}`ReadsBig` from the new connection of the environment:
the SELECT returns the rows of the database after the delete, also when the delete fails. Proof
sketch: {name}`runScriptStep_plainDelete_eq`; a write keeps the catalog, so each reached context
has the catalog of {name}`shop`, and {name}`big_after` applies. -/
theorem big_after_delete (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (modeled : ∀ entry ∈ deleteScript.statements, ∃ output next others,
      runScriptStep runContext env.clock 0 (db.raw.connection env.counters) entry.1 entry.2 =
        .continued output next others) :
    (do let _ ← send deleteScript; query bigScript rfl).check ReadsBig (ExecutionContext.initial db env) := by
  obtain ⟨statement, head, resolves⟩ : ∃ statement, deleteScript.statements = [(statement, [])] ∧
      resolveStatement runContext (shop.raw.connection {}).resolveState statement =
        .ok (.delete 1 (some (.compare .is (some .integer) (.column 1) (.literal .null) .binary)) [] [] none,
          (shop.raw.connection {}).resolveState) := ⟨_, rfl, by decide +kernel⟩
  have script : deleteScript = ⟨[(statement, [])]⟩ := by rw [← head]
  refine big_after _ _ ?_
  rw [script]
  have found := resolves
  rw [← shop_state db env schema] at found
  have present := Database.table_of_findTable db.raw _ 1 ordersShape (shop_found db schema).2
  have covered := RunStep.continues_iff.2 (modeled (statement, []) (by rw [head]; exact List.mem_singleton_self _))
  sql_run [found, covered, present]
  exact schema


/-- A21 contrast on {name}`partial_`, with the rows of native SQLite 3.51.0: from the start,
{name}`bigScript` returns the orders 1 and 3; after {name}`deleteScript`, which deletes order 3,
it returns order 1 alone, so the result from the start does not hold after the write. -/
example : (partial_.run (query bigScript rfl)).returnsResult
      (·.Perm [[.integer 1, .integer 10], [.null, .integer 7]]) ∧
    (partial_.run (do let _ ← send deleteScript; query bigScript rfl)).outputs =
      [.done 1, .rows [[.integer 1, .integer 10]]] := by
  decide +kernel

#print axioms big_at
#print axioms big_after
#print axioms big_after_delete

end SelectContextCases
