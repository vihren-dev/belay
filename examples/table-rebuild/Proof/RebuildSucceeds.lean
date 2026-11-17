import RebuildSucceedsCopy
import Belay.Sqlite.Programs.Claims.KeptRead
import Belay.Sqlite.Programs.Claims.SchemaSuccess

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! Success of the rebuild on every database whose original customers fit the STRICT table. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- For a database: every row of the customers fits the STRICT types of the new customers
({name}`LiteralData.typesFit` on {name}`strictShape`): an integer id, a name that is text or NULL, and an email
that is text or NULL. The rows are those of the table that the name {lit}`customers` finds, wherever it is. A
database without such a table satisfies it. -/
def StrictRows (db : Database) : Prop :=
  ∀ (position : Nat) (customers : Table), db.raw.tableNamed customersName = some (position, customers) →
    ∀ row ∈ customers.rows, LiteralData.typesFit strictShape row = true

/-- The rebuild succeeds on every database of the guide's schema for which each old customer
fits the new STRICT types. This covers every complete environment and every branch. A database
with a customer that does not fit is outside the premise. Proof sketch: the computed schema path
leaves only statement 3, the copy, to prove. The table frame tracks its source. CREATE TABLE
adds the empty destination row store. The copy law applies to those tables and the STRICT premise. -/
theorem makeStrict_succeeds :
    Succeeds makeStrict (fun db => db.raw.catalog = sample.raw.catalog ∧ StrictRows db) := by
  intro db ⟨pre, fits⟩ env complete
  obtain ⟨customers, named, _⟩ := Database.tableNamed_of_hasCatalog (schema := sample) pre
    (name := customersName) (position := 0) (by with_unfolding_all exact rfl)
  have start : (db.raw.connection env.counters).resolveState = sample.raw.connection.resolveState := by
    simp [Database.Raw.connection, Connection.resolveState, pre]
  apply sendStatements_succeeds_mixed (path := rebuildPath.1) (final := rebuildPath.2)
    rebuild_resolves env.clock 0 start
    ⟨db.valid, fun _ saved => by simp [Database.Raw.connection] at saved⟩ (Held customers)
    ⟨ResolveState.tableAtPrefix_zero (Database.tableNamed_some named).2, fun h => by omega⟩
  · intro n bound i c schema valid held output next others step found member ok
    refine ⟨tracks_step bound schema held.1 step member ok, ?_⟩
    intro third
    have two : n = 2 := by omega
    subst n
    obtain ⟨_, rfl, _, aligned, nextEq⟩ := runScriptStep_createTable
      (found := by with_unfolding_all exact resolutionAt 2 schema) step
    have length : c.state.database.catalog.length = 2 := by
      rw [show c.state.database.catalog = (schemaAt 2).catalog from congrArg ResolveState.catalog schema]
      with_unfolding_all rfl
    rw [single_next member, nextEq]
    simp [List.getD_eq_getElem?_getD, aligned, length]
  · intro n bound remaining i c schema valid held
    have onlyCopy : sample.raw.connection.resolveState.uncheckedSteps rebuildPath.1 = [3] := by decide +kernel
    rw [onlyCopy, List.mem_singleton] at remaining
    subst n
    obtain ⟨output, next, others, step, _, ok⟩ := copy_continues (clock := env.clock) (index := i)
      schema held valid (fits 0 customers named)
    exact ⟨output, next, others, step, ok⟩

#print axioms makeStrict_succeeds

end RebuildGuide
