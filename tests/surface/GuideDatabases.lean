import Belay

/-! A fixture of `tests/surface_guide_test.py`: the examples of the user guide's section
"Databases" over the surface's `Database` (`Belay/Sqlite/Database.lean`) and `db!`
(`Belay/Sqlite/DbBang.lean`). The file fails to elaborate when an example does not hold. -/

open Belay.Sqlite

-- `Database.empty` has no tables, so `db.rows` gives `none` for every name.
example : Database.empty.catalog = [] := rfl
example : Database.empty.rows "invoices" = none := by decide

/-- A database with the table `invoices(id)` and two rows, built with `db!`
(`Belay/Sqlite/DbBang.lean`), which proves it valid. -/
def twoInvoices : Database := db! r"CREATE TABLE invoices (id); INSERT INTO invoices VALUES (1), (2)"

-- `db.rows` reads a table by its name, with ASCII case ignored, and gives `none` for another name.
example : twoInvoices.rows "invoices" = some [[1], [2]] := by decide +kernel
example : twoInvoices.rows "INVOICES" = some [[1], [2]] := by decide +kernel
example : twoInvoices.rows "customers" = none := by decide +kernel

-- The facts of a valid database need no hypothesis.
example (db : Database) : db.raw.NotNull := db.notNull
example (db : Database) : db.raw.ChecksHold := db.check
example (db : Database) : db.raw.KeysUnique := db.unique
example (db : Database) : db.raw.RowidsDistinct := db.rowid_unique

-- `db.raw` is the plain database, and a valid database is admitted.
example (db : Database) : db.raw.Admitted Profile.pinned := db.valid.admitted
example (db : Database) : Database.Raw := db.raw
