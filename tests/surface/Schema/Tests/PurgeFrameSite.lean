import PurgeFrameQueries

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the site of the guide's purge claim (ADR 0017,
S6). The purge `DELETE FROM sessions WHERE customer_id = :c AND expires_at < :now` removes the rows for which the
filter is true. The claim compares the start with the reached database. It holds when the schema, the resolution of the
purge and of the claim, and the model of the purge are as the fields of `PurgeFrameSite` say. The final property of
the claim is not a field of the site. -/

set_option doc.verso true

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The conditions under which the purge deletes exactly the rows for which its filter is true, and the claim
reads the table of the start and the table of the reached database. The table {lit}`sessions` has three columns,
and its rowid alias is the first one. The purge resolves from the idle connection to a plain delete, which has no
rule of a trigger or a foreign key. The claim resolves against the catalog of the start and the same catalog of the
reached database, which a delete does not change. The model runs the purge for every clock and every counter. -/
structure PurgeFrameSite (db : Database) (c now : Value) where
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
  /-- The model runs the purge, whatever the clock and the counters. -/
  purgeModeled : ∀ env : Env, (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) purgeStatement
    [c, now]).continues = true

end AssertionExamples
