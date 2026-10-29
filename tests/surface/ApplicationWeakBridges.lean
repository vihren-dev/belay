import Belay
import ApplicationRestrictedDomain

/-! A fixture module of `tests/surface_application_test.py`: weak query translation is not enough
(ADR 0017, S8). A constant query and a migration that stores the clock value of its statement. Under a
clock that changes with the statement index, the weak translation of the read holds at the start context
and no full-state simulation exists. {lit}`ApplicationConstantClock` shows the bridge that works under a
clock with one date at every index. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace ApplicationWeakBridgesFixture
open Belay.Sqlite Belay.Sqlite.Calls ApplicationRestrictedDomainFixture
open Belay.Sqlite.Model hiding Database

/-- A clock with a new date at each statement index. -/
def daily : Env :=
  { clock := some (fun index => 212602449600000 + 86400000 * index), counters := Counters.newConnection }

/-- The start of a run under the changing clock. -/
def startDaily : ExecutionContext := ExecutionContext.initial sample daily

/-- The only context that the weak claims name under the changing clock: the start of the run. -/
def atDaily (state : ExecutionContext) : Prop := state = startDaily

/-- Under the changing clock the read translates weakly at the start context: the read and the read
after the migration give the same value and the same outputs. Proof sketch: both programs have one
branch, and the kernel evaluates the two actual runs. -/
theorem weak_translation_at_daily :
    Migration.TranslatesAt clockWrite atDaily (readPairing.old.run () ()) (readPairing.new.run () ())
      startDaily := by
  intro _
  apply Sql.View.ObservationEquivAt.of_one_branch
  · decide +kernel
  · decide +kernel
  · rfl

/-- Under the changing clock the weak translation does not give a full-state simulation, although it
holds at the start context ({name}`weak_translation_at_daily`). Plain words: no simulation of the read
pairing exists over the start context. Proof sketch: a simulation would commute at the start context. The
migration stores the date of statement 0 in one order and the date of statement 1 in the other, so the
stored rows differ; the kernel evaluates both actual runs. -/
theorem weak_translation_is_not_a_simulation : ¬ Simulation clockWrite atDaily readPairing := by
  intro simulation
  have same := simulation.commutes () () startDaily ⟨rfl, by decide +kernel⟩
  have rows := congrArg (fun observed => observed.2.connection.state.database.rowsAt 0) (observationProfile_actual same)
  have different :
      ((Migration.before (readPairing.old.run () ()) clockWrite).runFrom startDaily.clock startDaily.index
        startDaily.connection).connection.state.database.rowsAt 0 ≠
      ((Migration.after clockWrite (readPairing.new.run () ())).runFrom startDaily.clock startDaily.index
        startDaily.connection).connection.state.database.rowsAt 0 := by
    decide +kernel
  exact different rows

#print axioms weak_translation_at_daily
#print axioms weak_translation_is_not_a_simulation

end ApplicationWeakBridgesFixture
