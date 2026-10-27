import Belay

/-! A fixture module of `tests/surface_s6_rules_test.py`: a migration that stores the clock does not commute with a
read under a clock that changes (ADR 0017, S6). The commutation rule needs a clock that gives one date at every
statement index. Under a clock that changes, the migration runs at statement 1 after the read and at statement 0
before it, and stores two dates. The fixture shows that the premise fails and that the claim the rule would give is
false. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace S6RulesNegativeClock
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- One item. -/
def stamped : Database := db! r"
  CREATE TABLE items(id INTEGER PRIMARY KEY, name TEXT NOT NULL, qty INTEGER);
  INSERT INTO items VALUES(1, 'Ada', 5);"

/-- A clock that gives a new date from statement 1 on. -/
def movingClock : Env :=
  { clock := some (fun index => if index < 1 then 212602449600000 else 212602536000000)
    counters := Counters.newConnection }

/-- The migration stores the date of its statement. -/
def stampMigration : Script := sql r"UPDATE items SET qty = CURRENT_TIMESTAMP WHERE id = 1"

/-- A read that does not touch the stored column. -/
def lookupAda : Script := sql r"SELECT id FROM items WHERE name = 'Ada'"

/-- The start of the run under the moving clock. -/
def startMoving : ExecutionContext := ExecutionContext.initial stamped movingClock

/-- The moving clock does not give one date at every index, so the premise of the commutation rule fails.
Proof sketch: the dates of statements 0 and 1 differ. -/
theorem moving_clock_not_constant :
    ¬ ∀ assignment ∈ startMoving.clock, ∀ one other, assignment one = assignment other := by
  intro constant
  have := constant _ rfl 0 1
  revert this
  decide +kernel

/-- The read does not commute with the migration under the moving clock, although it reads no stored column that
the migration writes: the migration runs at statement 1 after the read and at statement 0 before it, and stores
two dates. Proof sketch: kernel evaluation of the two actual runs and comparison of the stored rows. -/
theorem moving_clock_not_commuting :
    ¬ Migration.CommutesAt (send stampMigration) (fun _ => True) (send lookupAda) startMoving := by
  intro same
  have inDomain : Migration.Domain (send stampMigration) (fun _ => True) startMoving :=
    ⟨True.intro, by decide +kernel⟩
  have rows := congrArg (fun observed => observed.2.connection.state.database.rowsAt 0) (same inDomain).actual
  have different :
      ((Migration.before (send lookupAda) (send stampMigration)).runFrom startMoving.clock startMoving.index
        startMoving.connection).connection.state.database.rowsAt 0 ≠
      ((Migration.after (send stampMigration) (send lookupAda)).runFrom startMoving.clock startMoving.index
        startMoving.connection).connection.state.database.rowsAt 0 := by
    decide +kernel
  exact different rows

#print axioms moving_clock_not_constant
#print axioms moving_clock_not_commuting

end S6RulesNegativeClock
