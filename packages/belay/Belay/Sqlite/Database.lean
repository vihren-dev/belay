import Belay.Sqlite.Values

set_option doc.verso true

/-! The surface's databases (ADR 0017, D3, amended 2026-10-22; ADR 0022, D5): a
{lit}`Database` holds a model database and its proof of {lit}`Database.Valid` under the pinned
profile, so a proof about it gets the facts of a valid database without a hypothesis.
{lit}`Database.Raw` is the model database without the proof. -/

namespace Belay.Sqlite

export Belay.Sqlite.Model (Profile Profile.pinned Catalog Database.Valid Database.Admitted
  Database.ForeignKeysHold Database.NotNull Database.ChecksHold Database.TypesFit Database.KeysUnique
  Database.RowidsDistinct)

/-- A database with its proof that it is valid under the pinned profile
({name}`Belay.Sqlite.Model.Profile.pinned`): every fact of an admitted database holds, and the
NOT NULL, CHECK, type and key constraints of every table hold. For example,
{lit}`Database.empty` has no tables. -/
structure Database where
  /-- The model database, without the proof. -/
  raw : Belay.Sqlite.Model.Database
  /-- The proof that the model database is valid under the pinned profile. -/
  valid : raw.Valid Profile.pinned

namespace Database

/-- The model database without the proof that it is valid. A claim that must also cover a
database that SQLite does not write with its statements, such as a file that another program
wrote, is stated over it, with the hypothesis {name}`Belay.Sqlite.Model.Database.Admitted`. -/
abbrev Raw := Belay.Sqlite.Model.Database

/-- The database without tables. -/
def empty : Database := ⟨{}, by decide⟩

/-- No NOT NULL column of the database holds NULL ({name}`Belay.Sqlite.Model.Database.NotNull`). -/
theorem notNull (db : Database) : db.raw.NotNull := db.valid.notNull

/-- The CHECK constraint of every table holds for every row
({name}`Belay.Sqlite.Model.Database.ChecksHold`). -/
theorem check (db : Database) : db.raw.ChecksHold := db.valid.check

/-- No two rows of a table conflict on a PRIMARY KEY, a UNIQUE constraint or a unique index
({name}`Belay.Sqlite.Model.Database.KeysUnique`). -/
theorem unique (db : Database) : db.raw.KeysUnique := db.valid.unique

/-- No two rows of a table share a rowid ({name}`Belay.Sqlite.Model.Database.RowidsDistinct`). -/
theorem rowid_unique (db : Database) : db.raw.RowidsDistinct := db.valid.rowid_unique

/-- The catalog of the database: its tables, columns, keys, constraints, indexes and triggers. -/
def catalog (db : Database) : Catalog := db.raw.catalog

/-- The rows of the named table, each as its values in column order, or
{lean}`(none : Option (List (List Value)))` when the database has no table of that name. The
name is matched as SQLite matches names, with ASCII case ignored. -/
def rows (db : Database) (name : String) : Option (List (List Value)) :=
  (db.raw.catalog.findTable (Belay.Sqlite.Model.Identifier.ofString name)).map fun (position, _) =>
    (db.raw.rows.getD position []).map (·.values)

end Database

end Belay.Sqlite
