import Belay.Sqlite.Model.Schema.Rows.ScriptRunConstraints

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every profile and database: it is valid under the profile ({name}`Database.Valid`) exactly when it is
admitted and satisfies the four constraint atoms ({name}`Database.ConstraintAtoms`). Proof sketch: the fields
of the structure. -/
theorem Database.valid_iff {profile : Profile} {database : Database} :
    database.Valid profile ↔ database.AdmittedWith profile Database.ConstraintAtoms :=
  ⟨fun valid => ⟨valid.admitted, valid.constraintAtoms⟩,
    fun ⟨admitted, notNull, typesFit, checks, unique⟩ => ⟨admitted, notNull, checks, typesFit, unique⟩⟩

/-- For every profile: the empty database ({lean}`({} : Database)`, with no table and no row) is valid
({name}`Database.Valid`). A new connection starts from it, so the corollary applies to every run on a new
connection. Proof sketch: the catalog is empty, so it is valid, and every atom about the tables holds
because the database has no table. -/
theorem Database.valid_empty (profile : Profile) : (({} : Database)).Valid profile := by
  have noTable : ∀ position, ({} : Database).table position = none := fun position => by
    simp [Database.table, Catalog.tableAt]
  have vacuous : ∀ {property : Nat → Table → Prop}, ({} : Database).EveryTable property :=
    fun position table present => by simp [noTable] at present
  exact ⟨⟨(rfl : Catalog.supported profile.limits [] = true), ⟨rfl, fun _ _ => rfl⟩, vacuous, vacuous, vacuous, vacuous,
    vacuous⟩, vacuous, vacuous, vacuous, vacuous⟩

end Belay.Sqlite.Model
