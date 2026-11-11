import Belay.Sqlite.Model.Queries.Preparation.InsertSelectKeeps
import Belay.Sqlite.Model.Schema.Columns.ValidAtomsStatement
import Belay.Sqlite.Model.Schema.Columns.KeysUniqueRunStep

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For the given database: it satisfies the four constraint atoms of {name}`Database.Valid`, each
for its own reading: {name}`Database.NotNull`, {name}`Database.TypesFit`, {name}`Database.ChecksHold`
and {name}`Database.KeysUnique`. It leaves out the facts of {name}`Database.Admitted`. -/
def Database.ConstraintAtoms (database : Database) : Prop :=
  database.NotNull ∧ database.TypesFit ∧ database.ChecksHold ∧ database.KeysUnique

/-- For every profile and database: a valid database ({name}`Database.Valid`) satisfies
{name}`Database.ConstraintAtoms`. Proof sketch: the four fields of the structure. -/
theorem Database.Valid.constraintAtoms {profile : Profile} {database : Database} (valid : database.Valid profile) :
    database.ConstraintAtoms :=
  ⟨valid.notNull, valid.typesFit, valid.check, valid.unique⟩

/-- The condition of a statement on the database for the four atoms together: the run condition of
"keys unique" ({name}`Resolved.Statement.RunCondition`: CREATE INDEX, ADD COLUMN and DROP) and the
conditions of "not null", "types fit" and "checks hold" for ADD COLUMN. All four hold. -/
def Resolved.Statement.AtomsCondition (database : Database) (statement : Resolved.Statement) : Prop :=
  statement.RunCondition database ∧ statement.NotNullCondition database ∧ statement.TypesFitCondition database ∧
    statement.ChecksHoldCondition database

/-- For every database and statement: if the statement has no run condition
({name}`Resolved.Statement.unconditioned`: it is not CREATE INDEX, ADD COLUMN or DROP), it meets
{name}`Resolved.Statement.AtomsCondition` on the database. Proof sketch: a case split on the
statement; each remaining case has four conditions that are {lit}`True`. -/
theorem Resolved.Statement.atomsCondition_of_unconditioned {database : Database} :
    ∀ {statement : Resolved.Statement}, statement.unconditioned = true → statement.AtomsCondition database := by
  intro statement unconditioned
  cases statement <;> first | exact ⟨trivial, trivial, trivial, trivial⟩ | exact nomatch unconditioned

end Belay.Sqlite.Model
