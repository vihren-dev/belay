import RebuildGuide

/-! A fixture module of {lit}`tests/surface_rebuild_test.py`: the rules of {lit}`sql_run` for CREATE TABLE, DROP TABLE,
a rename, a pragma setting, BEGIN and COMMIT (ADR 0017, S6, part 2). One program sends all of them to a database
with the schema of the guide. The hints close the resolution of each statement and the model's own evaluation closes
the other premises of the rules; the tactic reads the kind of each statement from the script. The claim says that a
program that sends no refused statement ends with no open transaction and with the settings that it sets. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

namespace SchemaRuleExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database
open RebuildGuide

/-- Every statement kind that has a rule for a schema or transaction statement: the setting off, a transaction, a
new table, the drop of another table, the rename of the new table, the commit and the setting on. -/
def allKinds : Script := sql r"
  PRAGMA foreign_keys = OFF;
  BEGIN;
  CREATE TABLE sessions_new (id INTEGER PRIMARY KEY, customer_id INTEGER NOT NULL, expires_at INTEGER NOT NULL);
  DROP TABLE sessions;
  ALTER TABLE sessions_new RENAME TO sessions;
  COMMIT;
  PRAGMA foreign_keys = ON;"

/-- After {name}`allKinds` on {name}`RebuildGuide.sample`, when no statement fails, no transaction is open and the
foreign-key enforcement is on. Plain words: the program of the six kinds leaves the connection with no open
transaction and with enforcement on. Proof: {lit}`sql_run` applies the rules of the six kinds in order; the
premises about the resolution of each statement are closed by evaluation, and the remaining goal is the claim about
the reached connection, which evaluation proves. -/
theorem allKinds_closes_the_transaction :
    FreshEnsures (send allKinds) (fun db => db = sample)
      (ifOk (fun final => ⌜final.connection.state.snapshot = none ∧ final.connection.foreignKeys = true⌝ :
        ContextAssertion)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db rfl env _
  sql_run [rfl]
  all_goals (intro _; exact ⟨rfl, rfl⟩)

#print axioms allKinds_closes_the_transaction

end SchemaRuleExamples
