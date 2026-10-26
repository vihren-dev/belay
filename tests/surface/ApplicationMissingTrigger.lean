import Belay
import ApplicationExpansion

/-! A fixture module of `tests/surface_application_test.py`: the missing-trigger bug (ADR 0017, S8). The
expansion of {lit}`ApplicationExpansion` without its two triggers fills the stored column for the rows
that exist, and leaves it empty for rows that a later write adds. An application that adds a customer
and then looks it up by the lowercase of the email finds it in the old interface and does not find it
after the broken expansion. The fixture keeps the kernel-checked witness, shows that the full expansion
does not have the bug on the same application, and shows that the relation which names the stored field
holds at the start and breaks after the write. It emits the two SQL replays of the witness for the
native check. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace ApplicationMissingTriggerFixture
open Belay.Sqlite Belay.Sqlite.Calls ApplicationExpansionFixture
open Belay.Sqlite.Model hiding Database

/-- The calls of the shop: add one customer, and look up the customer by the lowercase of the email. -/
inductive ShopCall where
  | addBob | findBob

/-- Both calls take no argument and give the outputs of their statement. -/
@[reducible] def shopSignature : Signature ShopCall where
  Argument _ := Unit
  Result _ := List Output

/-- The write that adds a customer. It names its columns, so it also works after the stored column
exists. -/
def addBob : Script := sql r"INSERT INTO customers(id, name, email) VALUES (2, 'Bob', 'Bob@X')"

/-- The lookup before the expansion, over the lowercase of the email. -/
def findOld : Script := sql r"SELECT id FROM customers WHERE lower(email) = lower('bob@x')"

/-- The lookup after the expansion, over the stored column. -/
def findNew : Script := sql r"SELECT id FROM customers WHERE email_lower = lower('bob@x')"

/-- The pairing: the write is shared, and the lookup changes. -/
def shopPairing : Pairing shopSignature where
  old := fun
    | .addBob => { script := fun _ => addBob, result := id }
    | .findBob => { script := fun _ => findOld, result := id }
  new := fun
    | .addBob => { script := fun _ => addBob, result := id }
    | .findBob => { script := fun _ => findNew, result := id }

/-- The application that adds the customer and looks it up. -/
def addThenFind : Application shopSignature (List Output) :=
  .call .addBob () fun _ => .call .findBob () fun found => .pure found

/-- The expansion without its two CREATE TRIGGER statements. -/
def buggyExpansion : Script := sql r"
  ALTER TABLE customers ADD COLUMN email_lower TEXT;
  UPDATE customers SET email_lower = lower(email);"

/-- The broken expansion succeeds at the first context. Proof sketch: kernel evaluation. -/
theorem buggy_domain : Migration.Domain (send buggyExpansion) (fun _ => True) initial :=
  ⟨True.intro, by decide +kernel⟩

/-- The witness. The application in the old interface finds the new customer (id 2). After the broken
expansion, the application in the new interface finds nothing. After the full expansion, it finds the
customer. Proof sketch: kernel evaluation of the three runs. -/
theorem missing_trigger_witness :
    ((addThenFind.interp shopPairing.old).runFrom initial.clock initial.index initial.connection).value =
      some [.rows [[.integer 2]]] ∧
    ((Migration.after (send buggyExpansion) (addThenFind.interp shopPairing.new)).runFrom initial.clock
      initial.index initial.connection).value = some [.rows []] ∧
    ((Migration.after (send expansion) (addThenFind.interp shopPairing.new)).runFrom initial.clock
      initial.index initial.connection).value = some [.rows [[.integer 2]]] := by
  decide +kernel

/-- The broken expansion does not translate the application, although it succeeds. Plain words: at the
first context the old application and the new application after the broken expansion have different
values. Proof sketch: the weak translation compares the values, which {name}`missing_trigger_witness`
separates. -/
theorem missing_trigger_is_not_a_translation :
    ¬ Migration.TranslatesAt (send buggyExpansion) (fun _ => True) (addThenFind.interp shopPairing.old)
      (addThenFind.interp shopPairing.new) initial := by
  intro claim
  have same := congrArg Prod.fst (claim buggy_domain).actual
  change ((addThenFind.interp shopPairing.old).runFrom initial.clock initial.index initial.connection).value =
    ((Migration.after (send buggyExpansion) (addThenFind.interp shopPairing.new)).runFrom initial.clock
      initial.index initial.connection).value at same
  rw [missing_trigger_witness.1, missing_trigger_witness.2.1] at same
  cases same

/-- Whether every row of the first table has a stored value that is not NULL. -/
def storedFilled (context : ExecutionContext) : Bool :=
  (context.connection.state.database.rowsAt 0).all fun row =>
    match row.values.getLast? with
    | some .null | none => false
    | some (.integer _) | some (.real _) | some (.text _) | some (.blob _) => true

/-- A relation that names the clock and requires the stored field of the new context to be filled. -/
def filledRelation (old new : ExecutionContext) : Prop := old.clock = new.clock ∧ storedFilled new = true

/-- The context that the quiet view gives after the actual run of the expansion without triggers. -/
def buggyMigrated : ExecutionContext :=
  (Sql.View.quiet (send buggyExpansion)).finish initial
    ((send buggyExpansion).runFrom initial.clock initial.index initial.connection)

/-- The relation holds at the migrated context of both expansions, so it passes the entry test of both.
Proof sketch: kernel evaluation of the stored fields. -/
theorem relation_holds_at_entry :
    filledRelation initial buggyMigrated ∧ filledRelation initial (migratedFrom initial) :=
  ⟨⟨rfl, by decide +kernel⟩, ⟨rfl, by decide +kernel⟩⟩

/-- After the write call, the stored field is filled in the world with triggers and is not filled in the
world without them. Proof sketch: kernel evaluation of the write on both migrated contexts. -/
theorem relation_after_write :
    storedFilled ((migratedFrom initial).finish
      ((shopPairing.new.run .addBob ()).runFrom (migratedFrom initial).clock (migratedFrom initial).index
        (migratedFrom initial).connection)) = true ∧
    storedFilled (buggyMigrated.finish
      ((shopPairing.new.run .addBob ()).runFrom buggyMigrated.clock buggyMigrated.index
        buggyMigrated.connection)) = false := by
  decide +kernel

/-- The relation holds at the start of the broken world and is not closed under the write call: the
shop pairing is not a scoped simulation under it. Proof sketch: the scoped agreement of the write at the
related pair requires the relation after the write, which {name}`relation_after_write` refutes. -/
theorem relation_is_not_closed : ¬ ScopedSimulation filledRelation shopPairing := by
  intro simulation
  have closed := (simulation .addBob () initial buggyMigrated relation_holds_at_entry.1).actual.2.2
  have filled := closed.2
  rw [relation_after_write.2] at filled
  cases filled

/-- The database that the expansion without triggers leaves: the field is filled for the old row. -/
def buggyDatabase : Belay.Sqlite.Database := db! r"
  CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL, email_lower TEXT);
  INSERT INTO customers VALUES(1, 'Ada', 'Alpha@X', 'alpha@x');"

/-- The text database is the database that the broken expansion reaches. Proof sketch: kernel
evaluation of the run and of the parsed database. -/
theorem buggy_database_is_reached :
    ((send buggyExpansion).runFrom initial.clock initial.index initial.connection).connection.state.database =
      buggyDatabase.raw := by
  decide +kernel

/-- The write and the stored lookup as one script. -/
def newWitness : Script := sql r"
  INSERT INTO customers(id, name, email) VALUES (2, 'Bob', 'Bob@X');
  SELECT id FROM customers WHERE email_lower = lower('bob@x');"

/-- The write and the original lookup as one script. -/
def oldWitness : Script := sql r"
  INSERT INTO customers(id, name, email) VALUES (2, 'Bob', 'Bob@X');
  SELECT id FROM customers WHERE lower(email) = lower('bob@x');"

/-- The two scripts give the outputs of the witness: the new script on the broken world finds nothing,
and the old script on the original world finds the customer. Proof sketch: kernel evaluation. -/
theorem witness_outputs :
    ((send newWitness).runFrom initial.clock initial.index
      ((send buggyExpansion).runFrom initial.clock initial.index initial.connection).connection).value =
        some [.done 1, .rows []] ∧
    ((send oldWitness).runFrom initial.clock initial.index initial.connection).value =
        some [.done 1, .rows [[.integer 2]]] := by
  decide +kernel

#print axioms buggy_domain
#print axioms missing_trigger_witness
#print axioms missing_trigger_is_not_a_translation
#print axioms relation_holds_at_entry
#print axioms relation_after_write
#print axioms relation_is_not_closed
#print axioms buggy_database_is_reached
#print axioms witness_outputs

open Lean Elab Meta in
/-- Keep exact model value tags so the test can compare native observations. -/
def outputJson : Output → Json
  | .rows rows => Json.mkObj [("rows", toJson rows)]
  | .done changes => Json.mkObj [("done", toJson changes)]
  | .error code => Json.mkObj [("error", toJson code)]
  | .oneOf results => Json.mkObj [("oneOf", toJson results)]
  | .unmodeled reason => Json.mkObj [("unmodeled", toJson reason)]

open Lean Elab Meta in
/-- Emit one replay of the S5 path: the SQL text, and the outputs that the model gives. -/
def emitReplay (name : String) (report : Replay.Report) : Term.TermElabM Unit := do
  logInfo m!"REPLAY:{(Json.mkObj [("name", toJson name), ("sql", toJson report.sqlite),
    ("outputs", toJson (report.outputs.map outputJson))]).compress}"

open Lean Elab Meta in
/-- Replay the old script on the original database and the new script on the broken database. -/
elab "report_missing_trigger_replays" : command => Command.liftTermElabM do
  emitReplay "old" (← Replay.scriptReport (mkConst ``ApplicationExpansionFixture.sample) (mkConst ``oldWitness))
  emitReplay "buggy" (← Replay.scriptReport (mkConst ``buggyDatabase) (mkConst ``newWitness))

report_missing_trigger_replays

end ApplicationMissingTriggerFixture
