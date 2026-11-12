import Belay

/-! A fixture of `tests/surface_assertion_examples_test.py`: a successful delete trigger may remove a row that the
delete does not name (ADR 0017, S6). The guide's purge removes the expired sessions of one customer. A claim that
a session of another customer survives the purge is false on a database with a trigger that deletes more. The
check reads the actual run of the statement, with its trigger, and only the state before and after through the
session id, so it needs no `before` schema. -/

set_option doc.verso true

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The purge of the guide: the expired sessions of one customer. -/
def purgeSessions (c now : Int64) : Script :=
  sql r"DELETE FROM sessions WHERE customer_id = $c AND expires_at < $now"

/-- The claim for one session: a session with the id exists. -/
def sessionExists (s : Int64) : Script := sql r"SELECT 1 FROM sessions WHERE id = $s"

/-- Two sessions, an expired one of customer 1 and a live one of customer 2, and a trigger that removes the
sessions of every other customer after a delete. -/
def sweeping : Database := db! r"
  CREATE TABLE sessions (id INTEGER PRIMARY KEY, customer_id INTEGER NOT NULL, expires_at INTEGER NOT NULL);
  INSERT INTO sessions VALUES (1, 1, 10);
  INSERT INTO sessions VALUES (2, 2, 100);
  CREATE TRIGGER sweep AFTER DELETE ON sessions BEGIN
    DELETE FROM sessions WHERE customer_id <> OLD.customer_id; END;"

/-- The same sessions without the trigger. -/
def plain : Database := db! r"
  CREATE TABLE sessions (id INTEGER PRIMARY KEY, customer_id INTEGER NOT NULL, expires_at INTEGER NOT NULL);
  INSERT INTO sessions VALUES (1, 1, 10);
  INSERT INTO sessions VALUES (2, 2, 100);"

/-- The final context of the purge from the fresh start of a database, with no clock and the counters of a new
connection. -/
def afterPurge (db : Database) (c now : Int64) : ExecutionContext :=
  let start := ExecutionContext.initial db { counters := Counters.newConnection }
  start.finish ((send (purgeSessions c now)).runFrom none 0 start.connection)

/-- With the trigger, the purge of customer 1 runs without an error and removes the session 2 of customer 2, which
the statement does not name. -/
theorem a_delete_trigger_removes_an_unrelated_session :
    Holds (sessionExists 2) sweeping ∧ (afterPurge sweeping 1 50).outputs.allOk = true ∧
    ¬ Holds.reached (sessionExists 2) (afterPurge sweeping 1 50) := by
  decide +kernel

/-- Without the trigger, the same purge keeps the session 2 and removes the expired session 1. -/
theorem without_the_trigger_the_other_session_stays :
    Holds (sessionExists 2) plain ∧ (afterPurge plain 1 50).outputs.allOk = true ∧
    Holds.reached (sessionExists 2) (afterPurge plain 1 50) ∧
    ¬ Holds.reached (sessionExists 1) (afterPurge plain 1 50) := by
  decide +kernel

#print axioms a_delete_trigger_removes_an_unrelated_session
#print axioms without_the_trigger_the_other_session_stays

end AssertionExamples
