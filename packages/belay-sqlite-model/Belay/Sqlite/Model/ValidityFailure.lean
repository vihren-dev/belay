import Belay.Sqlite.Model.DatabaseConstraintChecks

set_option doc.verso true

/-! The first atom of {name}`Belay.Sqlite.Model.Database.Valid` that a database does not
satisfy, so that an error can name it. Each atom is decided with its own instance, so the search
gives no atom exactly when the database is valid. -/

namespace Belay.Sqlite.Model

/-- One atom of {name}`Database.Valid`, in the order of its fields and of the fields of
{name}`Database.Admitted`. For example, {lean}`ValidityAtom.notNull` stands for
{name}`Database.NotNull`. -/
inductive ValidityAtom where
  /-- {name}`Catalog.Valid` under the profile's limits. -/
  | catalog
  /-- {name}`Database.RowsShaped`. -/
  | rowsShaped
  /-- {name}`Database.RowidsDistinct`. -/
  | rowidsDistinct
  /-- {name}`Database.RowidsInRange`. -/
  | rowidsInRange
  /-- {name}`Database.RowsWide`. -/
  | rowsWide
  /-- {name}`Database.RowsStored`. -/
  | rowsStored
  /-- {name}`Database.RowsAliased`. -/
  | rowsAliased
  /-- {name}`Database.NotNull`. -/
  | notNull
  /-- {name}`Database.ChecksHold`. -/
  | checksHold
  /-- {name}`Database.TypesFit`. -/
  | typesFit
  /-- {name}`Database.KeysUnique`. -/
  | keysUnique
  deriving Repr, DecidableEq

/-- The Lean name of the proposition of the atom, for a message. For example,
{assert}`ValidityAtom.notNull.name = "Database.NotNull"`. -/
def ValidityAtom.name : ValidityAtom → String
  | .catalog => "Catalog.Valid"
  | .rowsShaped => "Database.RowsShaped"
  | .rowidsDistinct => "Database.RowidsDistinct"
  | .rowidsInRange => "Database.RowidsInRange"
  | .rowsWide => "Database.RowsWide"
  | .rowsStored => "Database.RowsStored"
  | .rowsAliased => "Database.RowsAliased"
  | .notNull => "Database.NotNull"
  | .checksHold => "Database.ChecksHold"
  | .typesFit => "Database.TypesFit"
  | .keysUnique => "Database.KeysUnique"

/-- The first atom of {name}`Database.Valid` under the profile that the database does not
satisfy, in the order of {name}`ValidityAtom`, decided with the instance of each atom; or
{lean}`(none : Option ValidityAtom)` for a valid database. For example, a database with a NULL
in a NOT NULL column and no other failure gives {lean}`some ValidityAtom.notNull`. -/
def Database.failingAtom? (profile : Profile) (database : Database) : Option ValidityAtom :=
  if ¬database.catalog.Valid profile.limits then some .catalog
  else if ¬database.RowsShaped then some .rowsShaped
  else if ¬database.RowidsDistinct then some .rowidsDistinct
  else if ¬database.RowidsInRange then some .rowidsInRange
  else if ¬database.RowsWide then some .rowsWide
  else if ¬database.RowsStored then some .rowsStored
  else if ¬database.RowsAliased then some .rowsAliased
  else if ¬database.NotNull then some .notNull
  else if ¬database.ChecksHold then some .checksHold
  else if ¬database.TypesFit then some .typesFit
  else if ¬database.KeysUnique then some .keysUnique
  else none

/-- For every profile and database: {name}`Database.failingAtom?` gives no atom exactly when
the database satisfies {name}`Database.Valid` under the profile. So when it gives an atom, the
database is not valid. -/
theorem Database.failingAtom?_eq_none_iff (profile : Profile) (database : Database) :
    database.failingAtom? profile = none ↔ database.Valid profile := by
  constructor
  · intro none_found
    simp only [Database.failingAtom?] at none_found
    repeat (split at none_found; · cases none_found)
    simp only [Decidable.not_not] at *
    exact ⟨⟨by assumption, by assumption, by assumption, by assumption, by assumption, by assumption,
      by assumption⟩, by assumption, by assumption, by assumption, by assumption⟩
  · rintro ⟨⟨catalog, shaped, distinct, inRange, wide, stored, aliased⟩, notNull, checks, typesFit, unique⟩
    simp only [Database.failingAtom?, catalog, shaped, distinct, inRange, wide, stored, aliased, notNull, checks,
      typesFit, unique, not_true_eq_false, ite_false]

end Belay.Sqlite.Model
