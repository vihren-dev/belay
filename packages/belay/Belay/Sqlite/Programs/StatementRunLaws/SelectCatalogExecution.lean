import Belay.Sqlite.Schema.Dispatch.ReadAnalysis
import Belay.Sqlite.Programs.Scripts.Run

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- The query and the subqueries to which a statement resolves on the connection of the database, when
it resolves to a query; {lean}`(none : Option (Resolved.Query × List Resolved.Query))` for a prepare
error or any other statement. The result reads only the catalog of the database. -/
def Database.selectQuery? (db : Database) (statement : Syntax.Statement) :
    Option (Resolved.Query × List Resolved.Query) :=
  match resolveStatement runContext (db.raw.connection {}).resolveState statement with
  | .ok (.query query subqueries, _) => some (query, subqueries)
  | .ok (.createView .., _) | .ok (.createTable .., _) | .ok (.createIndex .., _) | .ok (.createTrigger .., _)
  | .ok (.addColumn .., _) | .ok (.drop .., _) | .ok (.rewrite _, _) | .ok (.dropColumn .., _) | .ok (.begin, _)
  | .ok (.commit, _) | .ok (.rollback, _) | .ok (.insert .., _) | .ok (.update .., _) | .ok (.upsert .., _)
  | .ok (.insertSelect .., _) | .ok (.delete .., _) | .ok (.prepareError _, _) | .ok (.setting .., _)
  | .error _ => none

/-- For every two databases with the same catalog and all counters, the resolution state of the connection
of the first with the counters is that of the connection of the second. Proof sketch: the state reads
only the catalog. -/
theorem Database.resolveState_of_catalog (db catalog : Database) (schema : db.HasCatalog catalog)
    (counters : Counters) : (db.raw.connection counters).resolveState = (catalog.raw.connection {}).resolveState := by
  simp only [Connection.resolveState, Database.Raw.connection]
  rw [show db.raw.catalog = catalog.raw.catalog from schema]

/-- For every database {lit}`db`, database {lit}`catalog` whose catalog {lit}`db` has, counters,
statement, query and subqueries: when the statement resolves on {lit}`catalog` to the query with the
subqueries ({name}`Database.selectQuery?`), it resolves to them on the connection of {lit}`db` with the
counters, with some state after it. Proof sketch: the resolution reads only the catalog
({name}`Database.resolveState_of_catalog`); the cases of {name}`Database.selectQuery?`. -/
theorem Database.resolve_of_selectQuery {db catalog : Database} (schema : db.HasCatalog catalog)
    (counters : Counters) {statement : Syntax.Statement} {query : Resolved.Query}
    {subqueries : List Resolved.Query} (resolved : catalog.selectQuery? statement = some (query, subqueries)) :
    ∃ after, resolveStatement runContext (db.raw.connection counters).resolveState statement =
      .ok (.query query subqueries, after) := by
  rw [Database.resolveState_of_catalog db catalog schema]
  unfold Database.selectQuery? at resolved
  split at resolved
  · cases resolved
    exact ⟨_, ‹_›⟩
  all_goals cases resolved

end Belay.Sqlite
