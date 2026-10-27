import Belay.Sqlite.Model.AdmittedAtomFrames
import Belay.Sqlite.Model.StatementStep
import Belay.Sqlite.Model.RowLocalFrame
import Belay.Sqlite.Model.OutlineKeyLaws

set_option doc.verso true

/-! The run of a rename statement for the statement theorems. A rewrite of the catalog
({lit}`Resolved.Statement.rewrite`) either stores a catalog with the outline of the catalog
({lit}`Catalog.keepsOutline`) and keeps every row, or fails as {lit}`ExecutionError.unmodeled`
and keeps the database. So a fact about a database that a change of names keeps holds after the
statement, and a theorem about all statements needs one case for it. -/

namespace Belay.Sqlite.Model

/-- For every clock value, counters, parameters, catalog, property and database: if the database
has the property, and the database with the catalog has it when the catalog has the outline of the
catalog of the database and selects the same parents ({name}`Catalog.selectedParents`), the effect of
{name}`runStatement` for the rewrite satisfies the property ({name}`Effect.Satisfies`). Proof sketch:
the run is {name}`step`, which stores the catalog when {name}`Catalog.keepsOutline` and else fails
with the input database. Success and {lit}`constraintFail` need the property. Every other error,
including the rejection as {lit}`ExecutionError.unmodeled`, puts no obligation on the database. -/
theorem runStatement_rewrite_satisfies (clock : Int) (counters : Counters) (parameters : List Value)
    (renamed : Catalog) {database : Database} {property : Database → Prop} (kept : property database)
    (stored : renamed.outline = database.catalog.outline → renamed.selectedParents = database.catalog.selectedParents →
      property { database with catalog := renamed }) :
    (runStatement clock counters parameters (.rewrite renamed) database).effect.Satisfies property := by
  simp only [runStatement, step]
  split
  · rename_i same
    exact Effect.satisfies_of_effectDatabase (stored (Catalog.keepsOutline_eq same).1 (Catalog.keepsOutline_eq same).2)
  · exact Effect.satisfies_of_database kept rfl

/-- For every atom that is a {name}`RowLocalAtom` and every database whose tables have it: the effect
of a rewrite satisfies "every table has the atom". Proof sketch:
{name}`runStatement_rewrite_satisfies` with {name}`Database.EveryTable.of_outline` and the
renaming fact of the atom. Success and {lit}`constraintFail` need the atom, and every other error,
including the rejection as {lit}`ExecutionError.unmodeled`, puts no obligation on the database. -/
theorem runStatement_rewrite_rowLocal {atom : Table → Prop} (rowLocal : RowLocalAtom atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (renamed : Catalog) {database : Database}
    (every : database.EachTable atom) :
    (runStatement clock counters parameters (.rewrite renamed) database).effect.Satisfies
      fun after => after.EachTable atom :=
  runStatement_rewrite_satisfies clock counters parameters renamed every fun same _ =>
    Database.EveryTable.of_outline (fun _ first second rows shapes holds => rowLocal.renamed first second holds rows shapes)
      every same

/-- For every atom that is a {name}`TableAtom` and every database whose tables have it: the effect of
a rewrite satisfies "every table has the atom". Proof sketch: as
{name}`runStatement_rewrite_rowLocal`. Success and {lit}`constraintFail` need the atom, and every
other error, including the rejection as {lit}`ExecutionError.unmodeled`, puts no obligation on the
database. -/
theorem runStatement_rewrite_tableAtom {atom : Table → Prop} (tableAtom : TableAtom atom) (clock : Int)
    (counters : Counters) (parameters : List Value) (renamed : Catalog) {database : Database}
    (every : database.EachTable atom) :
    (runStatement clock counters parameters (.rewrite renamed) database).effect.Satisfies
      fun after => after.EachTable atom :=
  runStatement_rewrite_satisfies clock counters parameters renamed every fun same _ =>
    Database.EveryTable.of_outline (fun _ first second rows shapes holds => tableAtom.renamed first second holds rows shapes)
      every same

end Belay.Sqlite.Model
