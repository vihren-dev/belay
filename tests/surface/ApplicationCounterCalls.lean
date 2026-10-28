import Belay
import ApplicationExpansion

/-! A fixture module of `tests/surface_application_test.py`: calls that break the scoped condition of the
expansion (ADR 0017, S8). The shared write call does not commute fully with the expansion, because the
trigger adds a change to the total. A call that reads the total changes, and a call that reads the clock
under a clock that changes with the statement index, each break the scoped call condition for the
relation of the lookup theorem. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace ApplicationCounterCallsFixture
open Belay.Sqlite Belay.Sqlite.Calls LowercaseFixture ApplicationExpansionFixture
open Belay.Sqlite.Model hiding Database


/-- The calls of the counter interface: the shared write, the read of the total changes, and the read
of the clock. -/
inductive CounterCall where
  | setEmail | totalChanges | currentTime

/-- Every call takes no argument and gives the outputs of its statement. -/
@[reducible] def counterSignature : Signature CounterCall where
  Argument _ := Unit
  Result _ := List Output

/-- The write that changes the email of the customer. -/
def updateEmail : Script := sql r"UPDATE customers SET email='Beta@X' WHERE id=1"

/-- The read of the total changes. -/
def readTotal : Script := sql r"SELECT total_changes()"

/-- The read of the clock. -/
def readClock : Script := sql r"SELECT CURRENT_TIMESTAMP"

/-- The interface that both sides share: each partner of a call is the call itself. -/
def sharedInterface : Interface counterSignature
  | .setEmail => { script := fun _ => updateEmail, result := id }
  | .totalChanges => { script := fun _ => readTotal, result := id }
  | .currentTime => { script := fun _ => readClock, result := id }

/-- The pairing of the shared interface with itself. -/
def counterPairing : Pairing counterSignature := ⟨sharedInterface, sharedInterface⟩

/-- No full-state simulation of the shared write exists over the first context, although the expansion
succeeds there. Plain words: running the write and then the expansion does not give the context that
the expansion and then the write give. Proof sketch: a simulation would commute at the first context.
The kernel evaluates both orders and finds the counters 3 and 4 (the trigger's own change). -/
theorem no_full_simulation :
    ¬ Simulation plan.migration (fun state => state = initial) counterPairing := by
  intro simulation
  have claim := simulation.commutes .setEmail () initial ⟨rfl, by decide +kernel⟩
  have counters := congrArg (fun observed => observed.2.connection.state.counters) (observationProfile_actual claim)
  have different :
      ((Migration.before (counterPairing.old.run .setEmail ()) plan.migration).runFrom initial.clock
        initial.index initial.connection).connection.state.counters ≠
      ((Migration.after plan.migration (counterPairing.new.run .setEmail ())).runFrom initial.clock
        initial.index initial.connection).connection.state.counters := by
    decide +kernel
  exact different counters

/-- The read of the total changes gives 1 at the first context and 2 at its migrated context. -/
theorem total_changes_differ :
    ((counterPairing.old.run .totalChanges ()).runFrom initial.clock initial.index initial.connection).outputs =
      [.rows [[.integer 1]]] ∧
    ((counterPairing.new.run .totalChanges ()).runFrom (migratedFrom initial).clock (migratedFrom initial).index
      (migratedFrom initial).connection).outputs = [.rows [[.integer 2]]] := by
  decide +kernel

/-- For every relation that relates the first context to its migrated context: the relation is not a
scoped simulation of the pairing with the read of the total changes. Plain words: the read gives
different outputs at the two related contexts, so the call condition fails for every such relation.
Proof sketch: the scoped agreement of the read at the related pair would equate the two outputs, which
{name}`total_changes_differ` refutes. -/
theorem total_changes_breaks_every_entry (related : ExecutionContext → ExecutionContext → Prop)
    (entry : related initial (migratedFrom initial)) : ¬ ScopedSimulation related counterPairing := by
  intro simulation
  have same := (simulation .totalChanges () initial (migratedFrom initial) entry).actual.2.1
  rw [total_changes_differ.1, total_changes_differ.2] at same
  cases same

/-- The relation of the lookup theorem relates the first context to its migrated context. Proof sketch:
the entry contract {name}`Plan.entry` at the actual run of the expansion, which returns. -/
theorem plan_relation_enters : plan.Related initial (migratedFrom initial) := by
  have run := Sql.Branch.actual plan.migration initial.clock initial.index initial.connection
  have returned := ((Sql.succeedsFrom_iff_branches _ _ _ _).mp original_domain.2 _ run).1
  obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp returned
  exact plan.entry initial original_domain _ run value hvalue

/-- The relation of the lookup theorem is not a scoped simulation once the interface reads the total
changes. -/
theorem lookup_relation_fails_with_total_changes : ¬ ScopedSimulation plan.Related counterPairing :=
  total_changes_breaks_every_entry _ plan_relation_enters

/-- A clock with a new date at each statement index. -/
def dailyEnvironment : Env :=
  { clock := some (fun index => 212602449600000 + 86400000 * index), counters := environment.counters }

/-- The first context of the sample under the changing clock. -/
def initialDaily : ExecutionContext := ExecutionContext.initial sample dailyEnvironment

/-- The first context under the changing clock is admitted and the expansion succeeds there. Proof
sketch: as {name}`original_domain`. -/
theorem daily_domain : Migration.Domain plan.migration plan.Admitted initialDaily := by
  obtain ⟨site⟩ := sample_has_site
  exact ⟨⟨Plan.Source.ofDatabase plan sample dailyEnvironment.counters site⟩, by decide +kernel⟩

/-- The relation of the lookup theorem relates the first context under the changing clock to its
migrated context. -/
theorem daily_relation_enters : plan.Related initialDaily (migratedFrom initialDaily) := by
  have run := Sql.Branch.actual plan.migration initialDaily.clock initialDaily.index initialDaily.connection
  have returned := ((Sql.succeedsFrom_iff_branches _ _ _ _).mp daily_domain.2 _ run).1
  obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp returned
  exact plan.entry initialDaily daily_domain _ run value hvalue

/-- The read of the clock gives different dates at the first context and at its migrated context,
because the expansion moved the statement index by four. -/
theorem clock_reads_differ :
    ((counterPairing.old.run .currentTime ()).runFrom initialDaily.clock initialDaily.index
      initialDaily.connection).outputs ≠
    ((counterPairing.new.run .currentTime ()).runFrom (migratedFrom initialDaily).clock
      (migratedFrom initialDaily).index (migratedFrom initialDaily).connection).outputs := by
  decide +kernel

/-- The relation of the lookup theorem is not a scoped simulation once the interface reads the clock
under a clock that changes with the statement index. Plain words: the relation names no statement
index, and the expansion moves it. Proof sketch: the scoped agreement of the clock read at the related
pair would equate two outputs that {name}`clock_reads_differ` separates. -/
theorem lookup_relation_fails_with_clock_read : ¬ ScopedSimulation plan.Related counterPairing := by
  intro simulation
  exact clock_reads_differ
    (simulation .currentTime () initialDaily (migratedFrom initialDaily) daily_relation_enters).actual.2.1

#print axioms no_full_simulation
#print axioms total_changes_differ
#print axioms total_changes_breaks_every_entry
#print axioms lookup_relation_fails_with_total_changes
#print axioms lookup_relation_fails_with_clock_read

open Lean Elab Meta in
/-- The retained SQL of the migration and the two reads, with the model's total changes, for the native
check. The kernel theorems above check the same executions. -/
elab "report_expansion_totals" : command => Command.liftTermElabM do
  let (_, setup) ← Replay.construction (mkConst ``sample)
  let migration ← Replay.scriptText (mkConst ``ApplicationExpansionFixture.expansion)
  let read ← Replay.scriptText (mkConst ``readTotal)
  logInfo m!"EXPANSION-TOTALS:{(Json.mkObj [("setup", toJson setup), ("migration", toJson migration.text),
    ("read", toJson read.text),
    ("old", toJson (((counterPairing.old.run .totalChanges ()).runFrom initial.clock initial.index
      initial.connection).connection.state.counters.totalChanges)),
    ("new", toJson (((counterPairing.new.run .totalChanges ()).runFrom (migratedFrom initial).clock
      (migratedFrom initial).index (migratedFrom initial).connection).connection.state.counters.totalChanges))]).compress}"

report_expansion_totals

end ApplicationCounterCallsFixture