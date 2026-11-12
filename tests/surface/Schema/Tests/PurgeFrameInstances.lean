import PurgeFrameClaims

/-! A fixture module of `tests/surface_assertion_examples_test.py`: instances of the purge frame claim (ADR 0017, S6).
The kernel checks that the site of `PurgeFrameSite` holds on a database of sessions, and then runs the purge from the
fresh start, for values that the claim must cover: NULL parameters, a text time and an integer time. The run is the
actual run of the purge with its trigger rules and its rollback; the claim is read with the actual two-state
observation over the start and the reached database. -/

set_option doc.verso true
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- Three sessions: an expired and a live session of customer 1, and an expired session of customer 2. -/
def sessions : Database := db! r"
  CREATE TABLE sessions (id INTEGER PRIMARY KEY, customer_id INTEGER NOT NULL, expires_at INTEGER NOT NULL);
  INSERT INTO sessions VALUES (1, 1, 10);
  INSERT INTO sessions VALUES (2, 2, 10);
  INSERT INTO sessions VALUES (3, 1, 100);"

/-- The catalog position and entry of {lit}`sessions` in {name}`sessions`. -/
def sessionsEntry : Nat × CatalogTable := (sessions.raw.catalog.findTable (name! "sessions")).get (by decide +kernel)

/-- The site of the purge in {name}`sessions` for two values, given that the model runs the purge with them. Every
other field holds for any values, as the kernel checks by evaluation. -/
def sessionsSite (c now : Value) (modeled : ∀ env : Env, (runScriptStep runContext env.clock 0
    (sessions.raw.connection env.counters) purgeStatement [c, now]).continues = true) :
    PurgeFrameSite sessions c now where
  position := sessionsEntry.1
  table := sessionsEntry.2
  names := ["id", "customer_id", "expires_at"]
  purgeAfter := (sessions.raw.connection {}).resolveState
  claimAfter := sessions.raw.catalog
  found := by decide +kernel
  keyAlias := by decide +kernel
  purgeResolves := by decide +kernel
  claimResolves := by decide +kernel
  purgeModeled := modeled

/-- The model runs the purge of {name}`sessions` for the customer 1 and the integer time 50, for every environment. -/
theorem modeledAtFifty : ∀ env : Env, (runScriptStep runContext env.clock 0 (sessions.raw.connection env.counters)
    purgeStatement [.integer 1, .integer 50]).continues = true := fun env => by with_unfolding_all rfl

/-- The site of the purge for the customer 1 and the integer time 50. -/
def fiftySite : PurgeFrameSite sessions (.integer 1) (.integer 50) := sessionsSite _ _ modeledAtFifty

/-- The final context of the purge from the fresh start of a database, with no clock and the counters of a new
connection. -/
def purgeFinal (db : Database) (c now : Value) : ExecutionContext :=
  let start := ExecutionContext.initial db { counters := Counters.newConnection }
  start.finish ((send (purge c now)).runFrom none 0 start.connection)

/-- The claim that a session with the id exists. -/
def sessionExists (s : Int64) : Script := sql r"SELECT 1 FROM sessions WHERE id = $s"

/-- The claim that the table has the given number of sessions. -/
def sessionCount (n : Int64) : Script := sql r"SELECT 1 WHERE (SELECT count(*) FROM sessions) = $n"

/-- The integer time: the purge removes the expired session 1 of customer 1, and the claim holds. -/
theorem integer_time_purges_the_expired_session : (purgeFinal sessions (.integer 1) (.integer 50)).outputs.allOk = true ∧
    Holds.reachedSince (purgeKeeps (.integer 1) (.integer 50)) sessions (purgeFinal sessions (.integer 1) (.integer 50)) ∧
    ¬ Holds.reached (sessionExists 1) (purgeFinal sessions (.integer 1) (.integer 50)) ∧
    Holds.reached (sessionExists 3) (purgeFinal sessions (.integer 1) (.integer 50)) := by decide +kernel

/-- The time as text, as the guide's second claim warns: a text is greater than every integer, so the comparison
{lit}`expires_at < 'text'` is true for every row. -/
def textTime : Value := .text "2026-10-20".toUTF8.toList

/-- With a NULL customer nothing is deleted, and the claim holds. -/
theorem null_customer_deletes_nothing : (purgeFinal sessions .null (.integer 50)).outputs.allOk = true ∧
    Holds.reachedSince (purgeKeeps .null (.integer 50)) sessions (purgeFinal sessions .null (.integer 50)) ∧
    Holds.reached (sessionCount 3) (purgeFinal sessions .null (.integer 50)) := by decide +kernel

/-- With a NULL time nothing is deleted, and the claim holds. -/
theorem null_time_deletes_nothing : (purgeFinal sessions (.integer 1) .null).outputs.allOk = true ∧
    Holds.reachedSince (purgeKeeps (.integer 1) .null) sessions (purgeFinal sessions (.integer 1) .null) ∧
    Holds.reached (sessionCount 3) (purgeFinal sessions (.integer 1) .null) := by decide +kernel

/-- With a text time the purge deletes every session of the customer, also the live session 3, so "only expired
sessions are deleted" is false. The frame claim still holds: the session 2 of customer 2 stays. -/
theorem text_time_deletes_every_session_of_the_customer : (purgeFinal sessions (.integer 1) textTime).outputs.allOk = true ∧
    Holds.reachedSince (purgeKeeps (.integer 1) textTime) sessions (purgeFinal sessions (.integer 1) textTime) ∧
    ¬ Holds.reached (sessionExists 3) (purgeFinal sessions (.integer 1) textTime) ∧
    Holds.reached (sessionExists 2) (purgeFinal sessions (.integer 1) textTime) := by decide +kernel

/-- The site holds for the NULL customer. -/
theorem null_customer_has_a_site : Nonempty (PurgeFrameSite sessions .null (.integer 50)) :=
  ⟨sessionsSite _ _ fun env => by with_unfolding_all rfl⟩

/-- The site holds for the NULL time. -/
theorem null_time_has_a_site : Nonempty (PurgeFrameSite sessions (.integer 1) .null) :=
  ⟨sessionsSite _ _ fun env => by with_unfolding_all rfl⟩

/-- The site holds for the text time. -/
theorem text_time_has_a_site : Nonempty (PurgeFrameSite sessions (.integer 1) textTime) :=
  ⟨sessionsSite _ _ fun env => by with_unfolding_all rfl⟩

/-- The purge with the time as a Lean integer, the convenience of the guide: the frame claim for the integer time is the
claim for the value of that integer. Proof sketch: {name}`purge_frame` at the value. -/
theorem purge_frame_typed (c : Value) (now : Int64) :
    FreshEnsuresFrom (send (purge c (.integer now.toInt))) (fun db => Nonempty (PurgeFrameSite db c (.integer now.toInt)))
      (fun start => ifOk (holdsSince start (purgeKeeps c (.integer now.toInt)))) :=
  purge_frame c (.integer now.toInt)

/-- The purge with OR for AND, the variant that the guide warns about. -/
def purgeOr := sql r"DELETE FROM sessions WHERE customer_id = :c OR expires_at < :now"

/-- The final context of the variant {name}`purgeOr` from the fresh start of a database. -/
def purgeOrFinal (db : Database) (c now : Value) : ExecutionContext :=
  let start := ExecutionContext.initial db { counters := Counters.newConnection }
  start.finish ((send (purgeOr c now)).runFrom none 0 start.connection)

/-- The variant runs without an error and deletes the live session 3 of customer 1 and the expired session 2 of
customer 2 too: the frame claim of the guide fails, with the same claim script as for the right purge. -/
theorem or_variant_breaks_the_frame_claim :
    (purgeOrFinal sessions (.integer 1) (.integer 50)).outputs.allOk = true ∧
    ¬ Holds.reachedSince (purgeKeeps (.integer 1) (.integer 50)) sessions
      (purgeOrFinal sessions (.integer 1) (.integer 50)) := by decide +kernel

/-- The condition with {lit}`NOT` instead of {lit}`IS NOT 1`, the trap that the guide describes. -/
def purgeKeepsNot (c now : Value) : Script :=
  sql r"SELECT 1 WHERE NOT EXISTS (SELECT * FROM before.sessions WHERE NOT (customer_id = $c AND expires_at < $now) EXCEPT SELECT * FROM sessions)"

/-- Two expired sessions of two customers. -/
def expiredSessions : Database := db! r"
  CREATE TABLE sessions (id INTEGER PRIMARY KEY, customer_id INTEGER NOT NULL, expires_at INTEGER NOT NULL);
  INSERT INTO sessions VALUES (1, 1, 10);
  INSERT INTO sessions VALUES (2, 2, 10);"

/-- The final context of a statement that deletes every session, from the fresh start of a database. -/
def deleteEverything (db : Database) : ExecutionContext :=
  let start := ExecutionContext.initial db { counters := Counters.newConnection }
  start.finish ((send (sql r"DELETE FROM sessions")).runFrom none 0 start.connection)

/-- With a NULL customer the variant with {lit}`NOT` is true although a statement deleted every session, because the
condition is NULL for the expired rows and requires nothing of them; the condition with {lit}`IS NOT 1` is false. -/
theorem not_instead_of_is_not_one_requires_nothing_for_null :
    (deleteEverything expiredSessions).outputs.allOk = true ∧
    Holds.reachedSince (purgeKeepsNot .null (.integer 50)) expiredSessions (deleteEverything expiredSessions) ∧
    ¬ Holds.reachedSince (purgeKeeps .null (.integer 50)) expiredSessions (deleteEverything expiredSessions) := by
  decide +kernel

/-- Sessions with a trigger that refuses every delete. -/
def refusing : Database := db! r"
  CREATE TABLE sessions (id INTEGER PRIMARY KEY, customer_id INTEGER NOT NULL, expires_at INTEGER NOT NULL);
  INSERT INTO sessions VALUES (1, 1, 10);
  INSERT INTO sessions VALUES (2, 2, 10);
  CREATE TRIGGER refuse BEFORE DELETE ON sessions BEGIN SELECT RAISE(ABORT, 'no deletes'); END;"

/-- When a trigger aborts the purge, the run has an error and the rollback leaves the start: every session is still
there. The triple of {name}`purge_frame` requires nothing of a run with an error; the actual run shows that the claim
holds there too. -/
theorem an_aborted_purge_rolls_back :
    (purgeFinal refusing (.integer 1) (.integer 50)).outputs.allOk = false ∧
    Holds.reachedSince (purgeKeeps (.integer 1) (.integer 50)) refusing (purgeFinal refusing (.integer 1) (.integer 50)) ∧
    Holds.reached (sessionCount 2) (purgeFinal refusing (.integer 1) (.integer 50)) := by decide +kernel

#print axioms integer_time_purges_the_expired_session
#print axioms null_customer_deletes_nothing
#print axioms null_time_deletes_nothing
#print axioms text_time_deletes_every_session_of_the_customer
#print axioms or_variant_breaks_the_frame_claim
#print axioms not_instead_of_is_not_one_requires_nothing_for_null
#print axioms an_aborted_purge_rolls_back
#print axioms fiftySite
#print axioms null_customer_has_a_site
#print axioms null_time_has_a_site
#print axioms text_time_has_a_site
#print axioms purge_frame_typed

end AssertionExamples
