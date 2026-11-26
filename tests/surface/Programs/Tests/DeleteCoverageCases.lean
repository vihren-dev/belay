import SelectJoinSupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

namespace DeleteCoverageCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectJoinCases (shop ordersShape shop_found shop_state)
open scoped Belay.Sqlite.Run.DeleteCoverage

/-- Extract the single statement of each concrete fixture for the step rule. -/
private def first (script : Script) (nonempty : 0 < script.statements.length := by decide +kernel) :=
  script.statements[0].1

/-- Give the tactic its two input facts for a DELETE from orders. -/
local macro "check_shop_delete " stmt:term ", " db:term ", " env:term ", " schema:term : tactic =>
  `(tactic|
    (have found : resolveStatement runContext (shop.raw.connection {}).resolveState $stmt =
        .ok (.delete 1 _ [] _ none, (shop.raw.connection {}).resolveState) := rfl
     rw [← shop_state $db $env $schema] at found
     have present := Database.table_of_findTable ($db).raw _ 1 ordersShape (shop_found $db $schema).2
     cover_delete (runScriptStep_plainDelete_eq (clock := ($env).clock) (index := 0) (parameters := []) found), present))

/-- The lookup subquery can use the customers table in any database with the shop schema. -/
@[local delete_row_fact] private theorem customers_present (db : Database) (schema : db.HasCatalog shop) :
    db.raw.table 0 = some ⟨SelectJoinCases.customersShape, db.raw.rows.getD 0 []⟩ :=
  Database.table_of_findTable db.raw _ 0 SelectJoinCases.customersShape (shop_found db schema).1

/-- The statement used to check absoluteAmount. -/
private def absoluteAmount := first (sql r"DELETE FROM orders WHERE abs(amount) > 5")

/-- Amounts other than the minimum signed integer permit the ABS comparison. -/
private theorem absoluteAmount_covered (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (bounded : ∀ r ∈ db.raw.rows.getD 1 [], r.values.getD 2 .null ≠ .integer (-(2^63))) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) absoluteAmount []).continues = true := by
  check_shop_delete absoluteAmount, db, env, schema

/-- The statement used to check jsonCustomer. -/
private def jsonCustomer := first (sql r"DELETE FROM orders WHERE json_extract(customer_id, '$.x') = 1")

/-- Successful extraction at {lit}`$.x` permits the JSON comparison, including a missing path. -/
private theorem jsonCustomer_covered (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (extracts : ∀ r ∈ db.raw.rows.getD 1 [], ∃ v, Json.extract (r.values.getD 1 .null) [.text [36, 46, 120]] = .ok v) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) jsonCustomer []).continues = true := by
  check_shop_delete jsonCustomer, db, env, schema

/-- The statement used to check customerLookup. -/
private def customerLookup := first (sql r"DELETE FROM orders WHERE customer_id IN (SELECT id FROM customers)")

/-- The customer lookup needs only the shop catalog. -/
private theorem customerLookup_covered (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) customerLookup []).continues = true := by
  check_shop_delete customerLookup, db, env, schema

/-- The statement used to check clockSubquery. -/
private def clockSubquery := first (sql r"DELETE FROM orders WHERE EXISTS (SELECT CURRENT_TIMESTAMP)")

/-- A supplied clock covers a clock read inside EXISTS. -/
private theorem clockSubquery_covered (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (tick : Clock) (clockKnown : env.clock = some tick) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) clockSubquery []).continues = true := by
  check_shop_delete clockSubquery, db, env, schema

/-- The statement used to check changeCount. -/
private def changeCount := first (sql r"DELETE FROM orders WHERE changes() > 0")

/-- A known change count covers a read of changes(). -/
private theorem changeCount_covered (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (count : Nat) (known : env.counters.changes = some count) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) changeCount []).continues = true := by
  check_shop_delete changeCount, db, env, schema

/-- The statement used to check currentTime. -/
private def currentTime := first (sql r"DELETE FROM orders WHERE CURRENT_TIMESTAMP IS NOT NULL")

/-- A supplied clock covers a direct timestamp read. -/
private theorem currentTime_covered (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (tick : Clock) (clockKnown : env.clock = some tick) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) currentTime []).continues = true := by
  check_shop_delete currentTime, db, env, schema

/-- The statement used to check nullCustomer. -/
private def nullCustomer := first (sql r"DELETE FROM orders WHERE customer_id IS NULL")

/-- A null test needs no additional data or environment fact. -/
private theorem nullCustomer_covered (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) nullCustomer []).continues = true := by
  check_shop_delete nullCustomer, db, env, schema

/-- The statement used to check absoluteCustomer. -/
private def absoluteCustomer := first (sql r"DELETE FROM orders WHERE abs(customer_id) <= 12")

/-- The ABS rule also covers another column, bound and comparison. -/
private theorem absoluteCustomer_covered (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (bounded : ∀ r ∈ db.raw.rows.getD 1 [], r.values.getD 1 .null ≠ .integer (-(2^63))) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) absoluteCustomer []).continues = true := by
  check_shop_delete absoluteCustomer, db, env, schema

/-- The statement used to check jsonAmount. -/
private def jsonAmount := first (sql r"DELETE FROM orders WHERE json_extract(amount, '$.y') <> 3")

/-- The extraction rule also covers another column and path. -/
private theorem jsonAmount_covered (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (extracts : ∀ r ∈ db.raw.rows.getD 1 [], ∃ v, Json.extract (r.values.getD 2 .null) [.text [36, 46, 121]] = .ok v) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) jsonAmount []).continues = true := by
  check_shop_delete jsonAmount, db, env, schema

/-- The statement used to check notInNames. -/
private def notInNames := first (sql r"DELETE FROM orders WHERE amount NOT IN (SELECT name FROM customers)")

/-- The lookup rule also covers NOT IN with a different projected column. -/
private theorem notInNames_covered (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) notInNames []).continues = true := by
  check_shop_delete notInNames, db, env, schema

/-- Nested calls compose without a premise on the stored values. -/
private def nested := first (sql r"DELETE FROM orders WHERE 3 < length(trim(amount))")

/-- Resolve and cover a comparison with two nested ordinary functions. -/
private theorem nested_covered (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) nested []).continues = true := by
  check_shop_delete nested, db, env, schema

/-- Place the partial call on the right of the comparison. -/
private def reversedAbs := first (sql r"DELETE FROM orders WHERE 5 < abs(amount)")

/-- The same column bound proves the reversed comparison. -/
private theorem reversedAbs_covered (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (bounded : ∀ r ∈ db.raw.rows.getD 1 [], r.values.getD 2 .null ≠ .integer (-(2^63))) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) reversedAbs []).continues = true := by
  check_shop_delete reversedAbs, db, env, schema

/-- A caller can register a success rule for a partial function. The evaluator checks the
nonnegative size against its limit before constructing the blob. -/
@[local delete_row_fact] private theorem zeroblobSucceeds (v : Value)
    (fits : ¬ Resolved.zeroblobLimit < (if v.toInt64 < 0 then 0 else v.toInt64)) :
    Resolved.CallSafety.Succeeds Resolved.ScalarFunction.zeroblob.apply [v] := by
  simp [Resolved.CallSafety.Succeeds, Resolved.ScalarFunction.apply, fits]

/-- Use the caller's contract inside another function. -/
private def nestedBlob := first (sql r"DELETE FROM orders WHERE length(zeroblob(amount)) > 0")

/-- The local contract covers each stored amount within the model's size limit. -/
private theorem nestedBlob_covered (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (fits : ∀ r ∈ db.raw.rows.getD 1 [], let n := (r.values.getD 2 .null).toInt64
      ¬ Resolved.zeroblobLimit < (if n < 0 then 0 else n)) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) nestedBlob []).continues = true := by
  check_shop_delete nestedBlob, db, env, schema

/-- The date argument is a conditional with a partial function in its tail. -/
private def conditionalDate := first (sql r"DELETE FROM orders WHERE date(iif(customer_id, abs(amount), 0)) > '2000-01-01'")

/-- Cover the date and IIF branches with the clock supplied and the ABS inputs bounded. -/
private theorem conditionalDate_covered (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (tick : Clock) (known : env.clock = some tick)
    (bounded : ∀ r ∈ db.raw.rows.getD 1 [], r.values.getD 2 .null ≠ .integer (-(2^63))) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) conditionalDate []).continues = true := by
  check_shop_delete conditionalDate, db, env, schema

#print axioms conditionalDate_covered
#print axioms nestedBlob_covered
#print axioms nested_covered
#print axioms reversedAbs_covered
#print axioms absoluteAmount_covered
#print axioms jsonCustomer_covered
#print axioms customerLookup_covered
#print axioms clockSubquery_covered
#print axioms changeCount_covered
#print axioms currentTime_covered
#print axioms nullCustomer_covered
#print axioms absoluteCustomer_covered
#print axioms jsonAmount_covered
#print axioms notInNames_covered

/-- A single stored order for the boundary cases. -/
private def oneOrder (customer amount : Value) : Model.Database :=
  shop.raw.setRows 1 [⟨1, [.integer 1, customer, amount]⟩]

/-- Evaluate the actual step independently of the tactic. -/
private def continuesOn (s : Syntax.Statement) (db : Model.Database) (env : Env := {}) : Bool :=
  (runScriptStep runContext env.clock 0 (Database.Raw.connection db env.counters) s []).continues

example : continuesOn absoluteAmount (oneOrder .null (.integer (-(2^63)))) = false := by decide +kernel
example : continuesOn absoluteAmount (oneOrder .null (.integer (-(2^63)+1))) = true := by decide +kernel
example : continuesOn jsonCustomer (oneOrder (.text "broken".toUTF8.toList) (.integer 7)) = false := by decide +kernel
example : continuesOn jsonCustomer (oneOrder (.text "{\"x\":1}".toUTF8.toList) (.integer 7)) = true := by decide +kernel
example : continuesOn jsonCustomer (oneOrder (.text "{}".toUTF8.toList) (.integer 7)) = true := by decide +kernel
example : continuesOn jsonCustomer (oneOrder .null (.integer 7)) = true := by decide +kernel
example : continuesOn clockSubquery shop.raw = false := by decide +kernel
example : continuesOn clockSubquery shop.raw (Env.atTime 212602449600000) = true := by decide +kernel
example : continuesOn changeCount shop.raw = false := by decide +kernel

end DeleteCoverageCases
