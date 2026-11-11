import Belay.Sqlite.Model.Programs.Scripts.StatementStep
import Belay.Sqlite.Model.Schema.Rows.TableAtomFrames
import Belay.Sqlite.Model.Schema.Ddl.OutlineKeyLaws

set_option doc.verso true

/-! The run of a rename statement for the statement theorems. A rewrite of the catalog
({lit}`Resolved.Statement.rewrite`) either stores a catalog with the outline of the catalog
({lit}`Catalog.sameOutline`) and keeps every row, or fails as {lit}`ExecutionError.unmodeled`
and keeps the database. So a fact about a database that a change of names keeps holds after the
statement, and a theorem about all statements needs one case for it. -/

namespace Belay.Sqlite.Model

/-- The contract of a rewrite that keeps the outline, for a proof about a rename that does not unfold
{name}`step`: the run succeeds, stores the catalog of the rewrite and keeps every row, so the rows, the rowids
and the cells of every table are those of the database before. Proof sketch: the guard of {name}`step` holds. -/
theorem step_rewrite_of_keeps (clock : Int) (counters : Counters) (parameters : List Value) {renamed : Catalog}
    {database : Database} (kept : database.catalog.sameOutline renamed = true) :
    step clock counters parameters (.rewrite renamed) database = .ok { database with catalog := renamed } := by
  simp [step, kept]

/-- The contract of a rewrite that does not keep the outline: the run fails as
{lit}`ExecutionError.unmodeled` and returns the database that it was given. Proof sketch: the guard of
{name}`step` fails. -/
theorem step_rewrite_of_not_keeps (clock : Int) (counters : Counters) (parameters : List Value) {renamed : Catalog}
    {database : Database} (rejected : database.catalog.sameOutline renamed = false) :
    step clock counters parameters (.rewrite renamed) database = .error (.unmodeled, database) := by
  simp [step, rejected]

/-- What a successful run of a rewrite tells: the catalog is the one of the rewrite, the rows are those of the
database before, and the catalog of the rewrite has the outline of the old one. Proof
sketch: case split on the guard of {name}`step`; the rejected case is an error. -/
theorem step_rewrite_ok (clock : Int) (counters : Counters) (parameters : List Value) {renamed : Catalog}
    {database after : Database} (ran : step clock counters parameters (.rewrite renamed) database = .ok after) :
    after.catalog = renamed ∧ after.rows = database.rows ∧ database.catalog.sameOutline renamed = true := by
  cases kept : database.catalog.sameOutline renamed
  · simp [step, kept] at ran
  · simp [step, kept] at ran
    subst ran
    exact ⟨rfl, rfl, rfl⟩

end Belay.Sqlite.Model
