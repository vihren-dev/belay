import RebuildGuide
import Belay.Sqlite.Programs.Claims.KeptReadCheck

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

open Belay.Sqlite
namespace RebuildGuide

/-- The rebuild preserves the read of all sessions on every database whose catalog is the guide's schema, for every
complete environment: where the rebuild succeeds on the database, the read before the rebuild and the read after it
give the same value and the same outputs, on the actual run and on every branch. The databases are unrestricted
otherwise: the customers and sessions can have any rows. Where the rebuild fails on a database, the claim requires
nothing. Proof sketch: the checked read law follows the original sessions table through the
rebuild and compares the certified SELECT before and after it. -/
theorem makeStrict_preserves_allSessions :
    Migration.QueryPreserves (send makeStrict) allSessions (fun db => db.raw.catalog = sample.raw.catalog) :=
  KeptRead.preserves_of_check (name! "sessions") (by decide +kernel)

#print axioms makeStrict_preserves_allSessions

end RebuildGuide
