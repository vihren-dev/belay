import Belay

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace MigrationExpansionCounter
open Belay.Sqlite

/-- One customer before the normalization column exists. The native replay creates
the same database with one INSERT, which establishes the initial counters below. -/
def sample : Database := db! r"
  CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  INSERT INTO customers VALUES(1, 'Ada', 'Alpha@X');"

/-- A complete environment matching the counters after the native setup INSERT.
The scripts read no clock; its supplied value still belongs to the full context. -/
def environment : Env :=
  { clock := some (fun _ => 0)
    counters := { changes := some 1, totalChanges := some 1, lastInsertRowid := some 1 } }

/-- The original context has a valid bundled database and an empty output prefix. -/
def initial : ExecutionContext := ExecutionContext.initial sample environment

/-- Add and fill the normalized field, then install both maintenance triggers.
The UPDATE trigger runs only when an assignment names the original email column. -/
def expansion : Script := sql r"
  ALTER TABLE customers ADD COLUMN email_lower TEXT;
  UPDATE customers SET email_lower = lower(email);
  CREATE TRIGGER customers_email_ins AFTER INSERT ON customers BEGIN
    UPDATE customers SET email_lower=lower(NEW.email) WHERE id=NEW.id; END;
  CREATE TRIGGER customers_email_upd AFTER UPDATE OF email ON customers BEGIN
    UPDATE customers SET email_lower=lower(NEW.email) WHERE id=NEW.id; END;"

/-- The same application updates one existing customer in either execution order. -/
def updateEmail : Script := sql r"UPDATE customers SET email='Beta@X' WHERE id=1"

/-- Run the application first, preserving its returned output list after expansion. -/
def beforeRun : SqlRun (List Output) :=
  (Migration.before (send updateEmail) (send expansion)).runFrom
    initial.clock initial.index initial.connection

/-- Run expansion first, then return the application's output list. -/
def afterRun : SqlRun (List Output) :=
  (Migration.after (send expansion) (send updateEmail)).runFrom
    initial.clock initial.index initial.connection

/-- Every input in this environment is known. Proof sketch: each optional field
contains a value, including the clock and all three connection counters. -/
theorem complete_environment : environment.Complete := ⟨rfl, rfl, rfl, rfl⟩

/-- Expansion succeeds at the original context on every permitted branch, so the
commutation counterexample lies inside the pattern's domain. Proof sketch: kernel
evaluation of the complete public success predicate on the four-statement script. -/
theorem original_domain : Migration.Domain (send expansion) (fun _ => True) initial := by
  exact ⟨True.intro, by decide +kernel⟩

/-- Both public runs finish without errors, return the same application outputs,
and expose only its one changed row through the migration views. Their five real
statements remain present in their ordinary traces. Proof sketch: kernel evaluation
of {name}`Sql.runFrom` and each view's projection on these concrete scripts. -/
theorem same_application_observations :
    beforeRun.outputs.allOk = true ∧ afterRun.outputs.allOk = true ∧
    beforeRun.value = some [.done 1] ∧ afterRun.value = some [.done 1] ∧
    (Migration.beforeView (send updateEmail) (send expansion)).project beforeRun.outputs = [.done 1] ∧
    (Migration.afterView (send expansion) (send updateEmail)).project afterRun.outputs = [.done 1] ∧
    beforeRun.outputs.length = 5 ∧ afterRun.outputs.length = 5 := by decide +kernel

/-- The complete final databases agree, including the new column and both triggers.
The one customer has the new email and its lowercase copy in either order.
Proof sketch: kernel evaluation of the two public runs. -/
theorem same_final_database :
    beforeRun.connection.state.database = afterRun.connection.state.database ∧
    (beforeRun.connection.state.database.rowsAt 0).map (·.values) =
      [[.integer 1, .text (bytes! "Ada"), .text (bytes! "Beta@X"),
        .text (bytes! "beta@x")]] := by decide +kernel

/-- Application-first counts setup, application and backfill: three changes.
Expansion-first also counts the trigger's UPDATE: four changes. Both report one
outer changed row and retain the setup rowid. Proof sketch: kernel evaluation of
the counters in the complete public executions, without bypassing support checks. -/
theorem different_totals :
    beforeRun.connection.state.counters =
      { changes := some 1, totalChanges := some 3, lastInsertRowid := some 1 } ∧
    afterRun.connection.state.counters =
      { changes := some 1, totalChanges := some 4, lastInsertRowid := some 1 } := by decide +kernel

/-- Full commutation fails at this admitted original context despite equal final
databases and application observations. Proof sketch: full actual equality would
equate the separately checked total-change counters 3 and 4. -/
theorem not_full_commutation :
    ¬ Migration.CommutesAt (send expansion) (fun _ => True) (send updateEmail) initial := by
  intro claim
  have same := congrArg (fun observed => observed.2.connection.state.counters)
    (claim original_domain).actual
  change beforeRun.connection.state.counters = afterRun.connection.state.counters at same
  rw [different_totals.1, different_totals.2] at same
  cases same

/-- The unrestricted fresh-context commutation claim is false. Proof sketch:
instantiate its universal database and complete-environment domain with this
valid one-row example, then use the fixed-context refutation. -/
theorem not_universal_commutation :
    ¬ Migration.Commutes (send expansion) (send updateEmail) (fun _ => True) := by
  intro claim
  exact not_full_commutation (claim sample True.intro environment complete_environment)

#print axioms complete_environment
#print axioms original_domain
#print axioms same_application_observations
#print axioms same_final_database
#print axioms different_totals
#print axioms not_full_commutation
#print axioms not_universal_commutation

open Lean Elab Meta

/-- Runtime observations for the pinned-native comparison. The kernel theorems
above check the same executions independently of this diagnostic serialization. -/
def report (run : SqlRun (List Output)) : Json :=
  Json.mkObj [
    ("rows", toJson ((run.connection.state.database.rowsAt 0).map (·.values))),
    ("total", toJson run.connection.state.counters.totalChanges),
    ("changed", toJson run.connection.state.counters.changes),
    ("last_id", toJson run.connection.state.counters.lastInsertRowid)]

/-- Retain the actual annotated SQL text with both model observations, so the native
check executes the same complete expansion. Existing replay validation checks that
the recovered text represents each actual script and the supplied database. -/
elab "report_expansion_counter" : command => Command.liftTermElabM do
  let (_, setup) ← Replay.construction (mkConst ``sample)
  let migration ← Replay.scriptText (mkConst ``expansion)
  let application ← Replay.scriptText (mkConst ``updateEmail)
  logInfo m!"MIGRATION-COUNTER:{(Json.mkObj [
    ("setup", toJson setup), ("migration", toJson migration.text),
    ("application", toJson application.text),
    ("before", report beforeRun), ("after", report afterRun)]).compress}"

report_expansion_counter

end MigrationExpansionCounter
