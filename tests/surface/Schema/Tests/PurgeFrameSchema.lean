import PurgeFrameClaims

set_option doc.verso true

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the guide's purge frame claim for each database
with the catalog of the pilot schema (ADR 0017, S6). The schema is the database {lit}`sessions` with one table
`sessions (id INTEGER PRIMARY KEY, customer_id INTEGER NOT NULL, expires_at INTEGER NOT NULL)`. The overview with
checked names is at the end of the file. -/

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

/-- For every database with the catalog of {name}`sessions`, the catalog has the table {lit}`sessions` at the
position of {name}`sessionsEntry`. Proof sketch: the premise fixes the catalog. -/
theorem sessions_found (db : Database) (schema : db.HasCatalog sessions) :
    db.raw.catalog.findTable (name! "sessions") = some sessionsEntry := by
  rw [show db.raw.catalog = sessions.raw.catalog from schema]
  decide +kernel

/-- The site of the purge in each database with the catalog of {name}`sessions`. Each field is a fact about the
catalog: the premise rewrites the catalog of the database to that of {name}`sessions`, and the kernel decides the
fact there. -/
def sessionsSite (db : Database) (schema : db.HasCatalog sessions) : PurgeFrameSite db where
  position := sessionsEntry.1
  table := sessionsEntry.2
  names := ["id", "customer_id", "expires_at"]
  purgeAfter := (sessions.raw.connection {}).resolveState
  claimAfter := sessions.raw.catalog
  found := sessions_found db schema
  keyAlias := by decide +kernel
  purgeResolves := by
    rw [Database.resolveState_of_catalog db sessions schema]
    decide +kernel
  claimResolves := by
    rw [show db.raw.catalog = sessions.raw.catalog from schema]
    decide +kernel

/-- The client statement of the guide's frame claim of the purge. Take two values, NULL and text included. Take an
admitted database with the catalog of {name}`sessions` and a complete environment. Run the purge from the fresh
start. After a run with no error, the reached database has each session of the start that the filter did not select.
The claim {name}`purgeKeeps` says this, with the start as its initial database. A run with an error requires
nothing. The statement has no premise other than the catalog. Proof sketch: {name}`purge_frame`
with the site {name}`sessionsSite`. -/
theorem purge_frame_on_sessions (c now : Value) :
    FreshEnsuresFrom (send (purge c now)) (·.HasCatalog sessions)
      (fun start => ifOk (holdsSince start (purgeKeeps c now))) :=
  fun db schema => purge_frame c now db ⟨sessionsSite db schema⟩

#print axioms sessions_found
#print axioms sessionsSite
#print axioms purge_frame_on_sessions

/-! Each database with the catalog of {name}`sessions` has the site of the purge ({name}`sessionsSite`). The client
statement {name}`purge_frame_on_sessions` follows from {name}`purge_frame`. It has no premise other than the
catalog. -/

end AssertionExamples
