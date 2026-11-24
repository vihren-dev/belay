import RebuildGuide
import Belay.Sqlite.Programs.Claims.KeptReadCheck

/-! The public check refuses a cascade into the protected table and a final read of a replacement table. -/

open Belay.Sqlite RebuildGuide
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

example : KeptRead.preservesCheck (name! "sessions") sample makeStrictWrongEnforced allSessions = false :=
  by decide +kernel

/-- The original table survives at its position under a new name. The final read
uses the replacement table and therefore has a different resolved statement. -/
private def replaceNamedTable : Script := sql r"
  ALTER TABLE sessions RENAME TO archived_sessions;
  CREATE TABLE sessions (id INTEGER PRIMARY KEY, customer_id INTEGER NOT NULL, expires_at INTEGER NOT NULL);"

example : KeptRead.preservesCheck (name! "sessions") sample replaceNamedTable allSessions = false :=
  by decide +kernel

/-- A sessions lookup whose bound id matters to the result. -/
private def sessionsById (id : Value) : Script := sql r"SELECT id FROM sessions WHERE id = ?1" id

/-- A check using id 2 as its reference proves preservation of the lookup for id 1.
The two scripts have distinct bindings. The actual step is compared to the reference
statement with the supplied values. Proof sketch: compute the reference check and
use the common syntax at each clock, index, connection and parameter list. -/
theorem checkedWithDifferentBindings :
    Migration.QueryPreserves (send makeStrict) (sessionsById (.integer 1)) (·.HasCatalog sample) := by
  apply KeptRead.preserves_of_check (name! "sessions") (sessionsById (.integer 2)) (by decide +kernel) (same := ?_)
  intro statement values single
  cases single
  exact ⟨_, _, rfl, fun _ _ _ _ => rfl⟩

#print axioms checkedWithDifferentBindings
