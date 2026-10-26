import Belay

/-! A fixture module of `tests/surface_application_test.py`: a restricted domain needs the domain
condition (ADR 0017, S8). The migration stores the clock value of its statement. The environment gives
the same date to statements 0 and 1, and another date from statement 2 on. One read call commutes with
the migration at the start context, because the migration finds the same date before and after the read.
The context after the read is not the start context, so the call does not keep the domain. The
application with two reads does not commute with the migration, because its migration step runs at
statement 2. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace ApplicationRestrictedDomainFixture
open Belay.Sqlite Belay.Sqlite.Calls
open Belay.Sqlite.Model hiding Database

/-- A table with one row for the migration to update. -/
def sample : Belay.Sqlite.Database := db! r"CREATE TABLE t(id INTEGER PRIMARY KEY, x INTEGER);
  INSERT INTO t VALUES (1, 1), (2, 2)"

/-- The statements 0 and 1 have one date, and the statements from 2 on have another date. -/
def steadyThenMoved : Env :=
  { clock := some (fun index => if index < 2 then 212602449600000 else 212602536000000)
    counters := Counters.newConnection }

/-- The only context that the simulation admits: the start of the run. -/
def start : ExecutionContext := ExecutionContext.initial sample steadyThenMoved

/-- The migration stores the date of its statement and sends no other statement. -/
def clockWrite : Sql Unit :=
  let (statement, values) := (sql r"UPDATE t SET x=CURRENT_TIMESTAMP WHERE id=1").statements[0]
  .exec statement values fun _ => .pure ()

/-- The call names of the interface: one read. -/
abbrev readSignature : Signature Unit where
  Argument _ := Unit
  Result _ := Nat

/-- The read sends a constant query and gives 7. -/
def readEntry : Entry Unit Nat := { script := fun _ => sql r"SELECT 1", result := fun _ => 7 }

/-- The pairing of the read with itself. -/
def readPairing : Pairing readSignature := ⟨fun _ => readEntry, fun _ => readEntry⟩

/-- An application with two reads. -/
def twoReads : Application readSignature Nat :=
  .call () () fun _ => .call () () fun last => .pure last

/-- The admitted contexts: only the start. -/
def atStart (state : ExecutionContext) : Prop := state = start

/-- The read commutes with the migration at the start: both orders store the same date and leave
the same complete context. Proof sketch: both programs have one branch, and the kernel evaluates
the two actual runs. -/
theorem read_commutes_at_start :
    Migration.CommutesAsAt clockWrite atStart (readPairing.old.run () ()) (readPairing.new.run () ()) start := by
  intro _
  apply Sql.View.EquivAt.of_one_branch
  · decide +kernel
  · decide +kernel
  · rfl

/-- The migration succeeds at the start context. Proof sketch: the kernel evaluates its one statement. -/
theorem migration_succeeds_at_start : Migration.Domain clockWrite atStart start :=
  ⟨rfl, by decide +kernel⟩

/-- The read does not keep the domain: after one read the context is not the start context, because
the statement index has moved. Proof sketch: the actual run of the read is a returning branch, and
its final context has index 1 while the start context has index 0. -/
theorem read_does_not_keep_domain :
    ¬ (readPairing.old.run () ()).ReturnsIn (Migration.Domain clockWrite atStart)
      (fun _ => Migration.Domain clockWrite atStart) := by
  intro keeps
  have after := keeps start migration_succeeds_at_start _ (Sql.Branch.actual _ _ _ _) 7 (by rfl)
  have index := congrArg (fun state : ExecutionContext => state.index) after.1
  have impossible : (1 : Nat) = 0 := index
  cases impossible

/-- No full-state simulation of the read pairing exists over the start context. Proof sketch: a
simulation contains the domain condition, which the previous theorem refutes. -/
theorem no_simulation_over_start : ¬ Simulation clockWrite atStart readPairing :=
  fun simulation => read_does_not_keep_domain (simulation.keepsDomain () ())

/-- The application with two reads does not commute with the migration at the start, although each
read commutes there. The migration after two reads runs at statement 2 and stores the second date; the
migration before them runs at statement 0 and stores the first. Proof sketch: compare the stored rows
of the two actual final connections. -/
theorem two_reads_do_not_commute :
    ¬ Migration.CommutesAsAt clockWrite atStart (twoReads.interp readPairing.old)
      (twoReads.interp readPairing.new) start := by
  intro same
  have rows := congrArg (fun observed => observed.2.connection.state.database.rowsAt 0)
    (same migration_succeeds_at_start).actual
  have different :
      ((Migration.before (twoReads.interp readPairing.old) clockWrite).runFrom start.clock start.index
        start.connection).connection.state.database.rowsAt 0 ≠
      ((Migration.after clockWrite (twoReads.interp readPairing.new)).runFrom start.clock start.index
        start.connection).connection.state.database.rowsAt 0 := by
    decide +kernel
  exact different rows

#print axioms read_commutes_at_start
#print axioms read_does_not_keep_domain
#print axioms no_simulation_over_start
#print axioms two_reads_do_not_commute

end ApplicationRestrictedDomainFixture
