import RebuildGuide

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! The third claim of the guide's table rebuild (ADR 0017, S6, part 3): the wrong rebuild does not keep the
sessions. With foreign keys on, the pragma inside the transaction does nothing, and {lit}`DROP TABLE customers` deletes
the sessions of every customer through {lit}`ON DELETE CASCADE`. {lit}`sql_refute` finds and certifies the
counterexample from the guide's schema. -/

open Belay.Sqlite
namespace RebuildGuide

/-- The wrong rebuild on a connection with foreign keys on does not preserve the sessions: on the sample
database it succeeds and the read gives its one session before the rebuild and none after it. Proof sketch:
{lit}`sql_refute` runs the model on the sample and certifies the counterexample. -/
theorem wrong_rebuild_loses_sessions : ¬ (requireNameWrongEnforced preserves allSessions) := by
  sql_refute with (db := sample)

#print axioms wrong_rebuild_loses_sessions

end RebuildGuide
