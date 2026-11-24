import PurgeFrameQueries

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the site of the guide's purge claim (ADR 0017,
S6). The purge `DELETE FROM sessions WHERE customer_id = :c AND expires_at < :now` removes the rows for which the
filter is true. The claim compares the start with the reached database. It holds when the schema and the resolution
of the purge and of the claim are as the fields of `PurgeFrameSite` say. The site does not assume that the model runs
the purge: the kind rule of the plain DELETE and the facts of its readiness give it ({name}`PurgeFrameSite.purge_continues`).
The final property of the claim is not a field of the site. -/

set_option doc.verso true

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The conditions under which the purge deletes exactly the rows for which its filter is true, and the claim
reads the table of the start and the table of the reached database. The table {lit}`sessions` has three columns,
and its rowid alias is the first one. The purge resolves from the idle connection to a plain delete, which has no
rule of a trigger or a foreign key. The claim resolves against the catalog of the start and the same catalog of the
reached database, which a delete does not change. No field depends on the values of the parameters. -/
structure PurgeFrameSite (db : Database) where
  /-- The catalog position of {lit}`sessions`. -/
  position : Nat
  /-- The catalog entry of {lit}`sessions`. -/
  table : CatalogTable
  /-- The names of the columns of the table. -/
  names : List String
  /-- The resolution state after the purge. -/
  purgeAfter : ResolveState
  /-- The catalog after the resolution of the claim. -/
  claimAfter : Catalog
  /-- The database has the table. -/
  found : db.raw.catalog.findTable (name! "sessions") = some (position, table)
  /-- The first column is the rowid alias. -/
  keyAlias : table.rowidAlias = some 0
  /-- The purge resolves to a plain delete with the filter of {name}`purgeFilter`. -/
  purgeResolves : resolveStatement runContext (db.raw.connection {}).resolveState purgeStatement =
    .ok (.delete position (some purgeFilter) [] [] none, purgeAfter)
  /-- The claim resolves to {name}`purgeKeepsResolved`. -/
  claimResolves : resolveTwoState runContext db.raw.catalog db.raw.catalog purgeKeepsParts.1 purgeKeepsParts.2 =
    .ok (purgeKeepsResolved position names, claimAfter)

/-- For every database with the site of the purge, environment and pair of values, the step of the purge from the
idle connection of the database with the counters of the environment continues. In plain words: the model runs the
purge for each clock, each set of counters and each pair of values, NULL and text included. Proof sketch: the kind
rule of the plain DELETE ({name}`runScriptStep_plainDelete_eq`) with the resolution of the site. The purge reads no
clock and no counter, the table is present, the purge has no subquery, and its filter is row-wise, so the check of
its readiness is true ({name}`deleteJsonReady_of_rowwise`). -/
theorem PurgeFrameSite.purge_continues {db : Database} (site : PurgeFrameSite db) (env : Env) (c now : Value) :
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) purgeStatement [c, now]).continues =
      true := by
  have calm : (Resolved.Statement.delete site.position (some purgeFilter) [] [] none).Calm := by
    intro expression member
    simp [Resolved.Statement.clockExpressions, Resolved.WriteRules.expressions] at member
    exact member ▸ purgeFilter_rowwise.calm
  have present : (db.raw.connection env.counters).state.database.table site.position = some _ :=
    Database.table_of_findTable db.raw _ _ _ site.found
  rw [runScriptStep_plainDelete_eq (connection := db.raw.connection env.counters) site.purgeResolves]
  simp [statementClock, calm.readsClock, calm.firstUnknown, present, Resolved.subqueriesPlain,
    deleteJsonReady_of_rowwise (filter := some purgeFilter) (by simpa using purgeFilter_rowwise),
    returningExpressions, RunStep.continues]

#print axioms PurgeFrameSite.purge_continues

end AssertionExamples
