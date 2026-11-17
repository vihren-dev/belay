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
