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

-- Schema success dispatch requires no evaluation of an abstract catalog.
example (state : ResolveState) (target : Nat) (name : Identifier) (table : CatalogTable) :
    (Resolved.Statement.createTable target name table).succeedsBySchema state = true := rfl
example (state : ResolveState) (renamed : Catalog) :
    (Resolved.Statement.rewrite renamed).succeedsBySchema state = true := rfl

-- A resolution equation and validity suffice even when the target and catalog are variables.
example (ctx : ExecutionContext) (stmt : Syntax.Statement) (target : Nat) (name : Identifier)
    (shape : CatalogTable) (after : ResolveState) (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.createTable target name shape, after)) :
    (send ⟨[(stmt, [])]⟩).check (fun outputs _ => outputs.all (fun o => !o.isError) = true) ctx := by
  obtain ⟨atEnd, aligned⟩ := step_guards_hold found rfl valid.1
  refine Sql.check_send_of_rule (runScriptStep_createTable_eq found) valid (by simp [atEnd, aligned, RunStep.continues])
    ?_
  simp only [atEnd, aligned, and_self, ite_true]
  refine Sql.sendReached_single ?_ fun _ => by simp [Output.isError]
  intro _ same
  cases same

-- The tactic proves the same claim with the kind rule: the validity of the connection gives the guards of the
-- step, so the premise that the step continues closes, and the case that remains is the success.
example (ctx : ExecutionContext) (stmt : Syntax.Statement) (target : Nat) (name : Identifier)
    (shape : CatalogTable) (after : ResolveState) (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.createTable target name shape, after)) :
    (send ⟨[(stmt, [])]⟩).check (fun outputs _ => outputs.all (fun o => !o.isError) = true) ctx := by
  sql_run [found]
  case success => rfl

example (ctx : ExecutionContext) (stmt : Syntax.Statement) (renamed : Catalog) (after : ResolveState)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.rewrite renamed, after)) :
    (send ⟨[(stmt, [])]⟩).check (fun outputs _ => outputs.all (fun o => !o.isError) = true) ctx := by
  apply Sql.check_send_rewrite valid found
  intro output next ok _ _ _
  simp [ok]

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
