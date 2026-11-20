import Belay.Sqlite.Model.Schema.Ddl.ResolveStatementFacts
import Belay.Sqlite.Model.Schema.Rows.DatabaseConstraints
import Belay.Sqlite.Model.Schema.Ddl.DatabaseDropColumn

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The catalog and row-store guards used by execution for a resolved statement.
* CREATE TABLE, VIEW and TRIGGER append at the end of aligned catalog and row lists.
* CREATE INDEX also reads an existing table. ADD COLUMN reads an existing table.
* A rewrite keeps the outline. DROP COLUMN passes {name}`Database.runsDropColumn`.
* Other statement kinds impose no guard here.

A separate data constraint can still fail, for example on duplicate keys of a UNIQUE index. -/
def Resolved.Statement.StepGuards (db : Database) : Resolved.Statement → Prop
  | .createTable pos .. | .createView pos .. | .createTrigger pos .. =>
    pos = db.catalog.length ∧ db.rows.length = db.catalog.length
  | .createIndex pos _ index =>
    pos = db.catalog.length ∧ db.rows.length = db.catalog.length ∧ (db.table index.table).isSome = true
  | .addColumn pos .. => (db.table pos).isSome = true
  | .rewrite renamed => db.catalog.sameOutline renamed = true
  | .dropColumn pos index stored => db.runsDropColumn pos index stored = true
  | .drop .. | .begin | .commit | .rollback | .insert .. | .update .. | .upsert ..
  | .insertSelect .. | .delete .. | .prepareError _ | .query .. | .setting _ _ => True

/-- For each statement resolved on the catalog of a valid database, its {name}`Resolved.Statement.StepGuards`
hold. Proof sketch: {name}`ResolverCertificate.link` supplies the catalog facts. Validity aligns the row
stores. A table lookup maps the catalog table to its stored rows. DROP COLUMN stores exactly the catalog
after dropping the column, so both outline checks compare it to itself. -/
theorem step_guards_hold {context : ResolveContext} {state after : ResolveState} {statement : Syntax.Statement}
    {resolved : Resolved.Statement} {database : Database} {profile : Profile}
    (found : resolveStatement context state statement = .ok (resolved, after))
    (same : state.catalog = database.catalog) (valid : database.Valid profile) :
    resolved.StepGuards database := by
  have link := (resolveStatement_certificate _ _ _ _ _ found).link _ (same ▸ valid.admitted.catalogSupported)
  rw [same] at link
  have aligned := valid.admitted.rowsShaped.1
  cases resolved <;> try trivial
  all_goals try exact ⟨link, aligned⟩
  case createIndex => exact ⟨link.1, aligned, by simpa [Database.table] using link.2⟩
  case addColumn => simpa [Resolved.Statement.StepGuards, Database.table] using link.1
  case dropColumn =>
    obtain ⟨droppable, rfl⟩ := link
    simp [Resolved.Statement.StepGuards, Database.runsDropColumn, droppable, Catalog.keepsOutline]

end Belay.Sqlite.Model
