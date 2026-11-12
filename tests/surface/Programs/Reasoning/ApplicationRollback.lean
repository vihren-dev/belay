import Belay
import ApplicationMissingTrigger

/-! A fixture module of `tests/surface_application_test.py`: the reverse direction (ADR 0017, S8). A
migration moves the email of each customer into a table of its own, and the new interface reads and
writes that table. A forward agreement of the two interfaces holds at the migrated start. After a
write of the new interface, a rollback that drops the new table loses the written email, and the old
interface reads a stale value. So the forward result does not give rollback safety, and no relation
that holds at the rolled-back context makes the reverse pairing a scoped simulation. The theorem
{lit}`ScopedSimulation.reverse` gives the call part, and the rollback needs an entry contract of its own. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace ApplicationRollbackFixture
open Belay.Sqlite Belay.Sqlite.Calls
open Belay.Sqlite.Model hiding Database

/-- One customer with an email in the table of customers. -/
def before : Belay.Sqlite.Database := db! r"
  CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT, email TEXT);
  INSERT INTO customers VALUES(1, 'Ada', 'a@x');"

/-- The first context of the database. All inputs are known after the setup INSERT. -/
def initial : ExecutionContext :=
  ExecutionContext.initial before
    { clock := some (fun _ => 0)
      counters := { changes := some 1, totalChanges := some 1, lastInsertRowid := some 1 } }

/-- The migration: a table of emails that holds a copy of the email of the customer. -/
def split : Sql (List Output) :=
  send (sql r"CREATE TABLE emails(id INTEGER PRIMARY KEY, email TEXT); INSERT INTO emails VALUES(1, 'a@x')")

/-- The rollback: it drops the table of emails. -/
def rollback : Sql (List Output) := send (sql r"DROP TABLE emails")

/-- The whole history as one script: the migration, the new write and read, the rollback, and the old
read. -/
def rollbackScript : Script := sql r"
  CREATE TABLE emails(id INTEGER PRIMARY KEY, email TEXT);
  INSERT INTO emails VALUES(1, 'a@x');
  UPDATE emails SET email = 'b@x' WHERE id = 1;
  SELECT email FROM emails WHERE id = 1;
  DROP TABLE emails;
  SELECT email FROM customers WHERE id = 1;"

/-- The two calls of the interface: the write of the email and its read. -/
inductive EmailCall where
  | setEmail | getEmail

/-- Both calls take no argument and give the outputs of their statement. -/
@[reducible] def emailSignature : Signature EmailCall where
  Argument _ := Unit
  Result _ := List Output

/-- The interface before the migration: the email is a column of the customer. -/
def oldEmails : Interface emailSignature
  | .setEmail => { script := fun _ => sql r"UPDATE customers SET email = 'b@x' WHERE id = 1", result := id }
  | .getEmail => { script := fun _ => sql r"SELECT email FROM customers WHERE id = 1", result := id }

/-- The interface after the migration: the email is a row of the table of emails. -/
def newEmails : Interface emailSignature
  | .setEmail => { script := fun _ => sql r"UPDATE emails SET email = 'b@x' WHERE id = 1", result := id }
  | .getEmail => { script := fun _ => sql r"SELECT email FROM emails WHERE id = 1", result := id }

/-- The pairing of the two interfaces. -/
def emailPairing : Pairing emailSignature := ⟨oldEmails, newEmails⟩

/-- The context that the quiet view gives after the actual run of a migration from a context. -/
def reachedBy (migration : Sql (List Output)) (state : ExecutionContext) : ExecutionContext :=
  (Sql.View.quiet migration).finish state (migration.runFrom state.clock state.index state.connection)

/-- The context after the migration. -/
def migrated : ExecutionContext := reachedBy split initial

/-- The context after the new write of the email, from the migrated context. -/
def afterWrite : ExecutionContext :=
  migrated.finish ((emailPairing.new.run .setEmail ()).runFrom migrated.clock migrated.index migrated.connection)

/-- The context after the rollback, from the context after the write. -/
def rolledBack : ExecutionContext := reachedBy rollback afterWrite

/-- At the migrated start, the read of the email agrees in both interfaces under the relation that
requires nothing of the contexts. Plain words: both reads give the same outputs and the same value, and
every branch of one has a matching branch of the other. Proof sketch: each program has one branch, and
the two actual runs have equal outputs. -/
theorem forward_reads_agree_at_the_start :
    Sql.ScopedAt (fun _ _ => True) (emailPairing.old.run .getEmail ()) (emailPairing.new.run .getEmail ())
      initial migrated := by
  refine Sql.ScopedAt.of_one_branch (by decide +kernel) (by decide +kernel) ⟨?_, ?_, trivial⟩ <;>
    decide +kernel

/-- The rollback loses the write. The new interface reads the written email at the context after the
write, and the old interface reads the old email at the rolled-back context. -/
theorem rollback_loses_the_write :
    ((emailPairing.new.run .getEmail ()).runFrom afterWrite.clock afterWrite.index afterWrite.connection).outputs =
      [.rows [[.text (bytes! "b@x")]]] ∧
    ((emailPairing.old.run .getEmail ()).runFrom rolledBack.clock rolledBack.index rolledBack.connection).outputs =
      [.rows [[.text (bytes! "a@x")]]] := by
  decide +kernel

/-- The rollback succeeds at the context after the write, so the loss is not a failure of the rollback.
Proof sketch: kernel evaluation of the success check. -/
theorem rollback_succeeds : rollback.SucceedsFrom afterWrite.clock afterWrite.index afterWrite.connection := by
  decide +kernel

/-- No relation that relates the context after the write to the rolled-back context makes the reverse
pairing a scoped simulation. Plain words: whatever the relation says, the read of the email gives
different outputs at the two related contexts. Proof sketch: the scoped agreement of the read at the
related pair would equate the two outputs, which {name}`rollback_loses_the_write` separates. -/
theorem rollback_breaks_every_entry (related : ExecutionContext → ExecutionContext → Prop)
    (entry : related afterWrite rolledBack) : ¬ ScopedSimulation related emailPairing.swap := by
  intro simulation
  have same : ((emailPairing.new.run .getEmail ()).runFrom afterWrite.clock afterWrite.index
      afterWrite.connection).outputs = ((emailPairing.old.run .getEmail ()).runFrom rolledBack.clock
      rolledBack.index rolledBack.connection).outputs :=
    (simulation .getEmail () afterWrite rolledBack entry).actual.2.1
  rw [rollback_loses_the_write.1, rollback_loses_the_write.2] at same
  cases same

#print axioms forward_reads_agree_at_the_start
#print axioms rollback_loses_the_write
#print axioms rollback_succeeds
#print axioms rollback_breaks_every_entry

open Lean Elab Meta in
/-- Replay the migration, the new write and read, the rollback, and the old read with the S5 path. -/
elab "report_rollback_replay" : command => Command.liftTermElabM do
  ApplicationMissingTriggerFixture.emitReplay "rollback"
    (← Replay.scriptReport (mkConst ``before) (mkConst ``rollbackScript))

report_rollback_replay

end ApplicationRollbackFixture
