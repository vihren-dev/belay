import Belay.Sqlite.Model.Schema.Columns.AtomsConditionsOfLink

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For the given profile and property of databases: the database is admitted under the profile
({name}`Database.Admitted`) and has the property. It is the invariant of the run theorems of
{lit}`runScriptAllFrom` for the atoms of slices 2 and 3. -/
abbrev Database.AdmittedWith (profile : Profile) (property : Database → Prop) (database : Database) : Prop :=
  database.Admitted profile ∧ property database

end Belay.Sqlite.Model
