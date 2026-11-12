import Belay.Sqlite.Model.Schema.Dispatch.StatementStep
import Belay.Sqlite.Model.Schema.Rows.TableAtomFrames
import Belay.Sqlite.Model.Schema.Ddl.OutlineKeyLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every clock value, counters, parameters, catalog, property and database: if the database
has the property, and the database with the catalog has it when the catalog has the outline of the
catalog of the database, the effect of
{name}`runStatement` for the rewrite satisfies the property ({name}`Effect.Satisfies`). A fact that also needs
the same selected parents ({name}`Catalog.selectedParents`) takes them as a premise of the property. Proof sketch:
the run is {name}`step`, which stores the catalog when {name}`Catalog.sameOutline` and else fails
with the input database. Success and {lit}`constraintFail` need the property. Every other error,
including the rejection as {lit}`ExecutionError.unmodeled`, puts no obligation on the database. -/
theorem runStatement_rewrite_satisfies (clock : Int) (counters : Counters) (parameters : List Value)
    (renamed : Catalog) {database : Database} {property : Database → Prop} (kept : property database)
    (stored : renamed.outline = database.catalog.outline → property { database with catalog := renamed }) :
    (runStatement clock counters parameters (.rewrite renamed) database).effect.Satisfies property := by
  simp only [runStatement, step]
  split
  · rename_i same
    exact Effect.satisfies_of_effectDatabase (stored (Catalog.sameOutline_eq same))
  · exact Effect.satisfies_of_database kept rfl

/-- For every atom that is a {name}`TableAtom` and every database whose tables have it: the effect of
a rewrite satisfies "every table has the atom". Proof sketch: {name}`runStatement_rewrite_satisfies` and
{name}`Database.EveryTable.of_outline` with the atom's renaming fact. Success and {lit}`constraintFail` need the atom, and every
other error, including the rejection as {lit}`ExecutionError.unmodeled`, puts no obligation on the
database. -/
theorem runStatement_rewrite_tableAtom {atom : Table → Prop} (tableAtom : TableAtom atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (renamed : Catalog) {database : Database}
    (every : database.EachTable atom) :
    (runStatement clock counters parameters (.rewrite renamed) database).effect.Satisfies
      fun after => after.EachTable atom :=
  runStatement_rewrite_satisfies clock counters parameters renamed every fun same =>
    Database.EveryTable.of_outline (fun _ first second rows shapes holds => tableAtom.renamed first second holds rows shapes)
      every same

end Belay.Sqlite.Model
