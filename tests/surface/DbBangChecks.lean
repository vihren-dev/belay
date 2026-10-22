import Belay

/-! A fixture of `tests/surface_guide_test.py`: checks of the model functions that `db!` uses for
its errors. They cover `ExecutionError.message` (`Model/ExecutionMessages.lean`) for each
constructor, `Database.failingAtom?` (`Model/ValidityFailure.lean`) on plain databases that are
not valid, `ValidityAtom.name` for each atom, and the term or error that `db!` gives for a
database (`databaseTerm` and `invalidDatabaseMessage` of `Belay/Sqlite/DbBang.lean`). The file fails to elaborate when a check fails. -/

open Belay.Sqlite
open Belay.Sqlite.Model (ExecutionError ValidityAtom constraintFailedMessage functionFailedMessage unmodeledHere)

-- SQLite 3.51's texts, where the model keeps what the message says.
#guard (ExecutionError.prepare (.expression (.noSuchColumn (name! "nmae")))).message .commit ==
  "no such column: nmae"
#guard ExecutionError.transactionAlreadyActive.message .begin == "cannot start a transaction within a transaction"
#guard ExecutionError.noActiveTransaction.message .commit == "cannot commit - no transaction is active"
#guard ExecutionError.noActiveTransaction.message .rollback == "cannot rollback - no transaction is active"
#guard ExecutionError.integerOverflow.message .commit == "integer overflow"
#guard ExecutionError.datatypeMismatch.message .commit == "datatype mismatch"
#guard ExecutionError.nullColumnDefault.message .commit == "Cannot add a NOT NULL column with default value NULL"
#guard ExecutionError.nonConstantColumnDefault.message .commit == "Cannot add a column with non-constant default"
#guard ExecutionError.checkColumnDefault.message .commit == "CHECK constraint failed"
-- The texts that are not SQLite's message for the statement.
#guard ExecutionError.constraintViolation.message .commit == "constraint failed; the model does not name the " ++
  "constraint that fails. Run the statement in the sqlite3 shell to see SQLite's message"
#guard ExecutionError.constraintFail.message .commit == constraintFailedMessage
#guard ExecutionError.constraintRollback.message .commit == constraintFailedMessage
#guard ExecutionError.functionError.message .commit == functionFailedMessage
#guard ExecutionError.unmodeled.message .commit == unmodeledHere

/-- A table `t(a, b NOT NULL)` with a PRIMARY KEY on `a`, and two rows. -/
def pair : Database := db! r"CREATE TABLE t (a PRIMARY KEY, b NOT NULL); INSERT INTO t VALUES (1, 'x'), (2, 'y')"

/-- The rows of `pair` with a NULL in the NOT NULL column `b`. -/
def nullInNotNull : Database.Raw :=
  pair.raw.setRows 0 [{ rowid := 1, values := [1, .null] }, { rowid := 2, values := [2, "y"] }]

/-- The rows of `pair` with the key `a` 1 twice. -/
def duplicateKey : Database.Raw :=
  pair.raw.setRows 0 [{ rowid := 1, values := [1, "x"] }, { rowid := 2, values := [1, "y"] }]

/-- The rows of `pair` with the rowid 1 twice. -/
def duplicateRowid : Database.Raw :=
  pair.raw.setRows 0 [{ rowid := 1, values := [1, "x"] }, { rowid := 1, values := [2, "y"] }]

/-- A STRICT table `s(a INTEGER CHECK (a < 5))` with one row. -/
def strictChecked : Database := db! r"CREATE TABLE s (a INTEGER CHECK (a < 5)) STRICT; INSERT INTO s VALUES (1)"

/-- The row of `strictChecked` with `7`, an integer that fails the CHECK constraint only. -/
def checkOnly : Database.Raw := strictChecked.raw.setRows 0 [{ rowid := 1, values := [7] }]

/-- The row of `strictChecked` with `1.5`, a real that does not fit the STRICT type and passes
the CHECK constraint. -/
def typeOnly : Database.Raw := strictChecked.raw.setRows 0 [{ rowid := 1, values := [.real (1.5 : Float).toBits] }]

/-- The row of `strictChecked` with `'x'`, a text that fails both the STRICT type and the CHECK
constraint, because a text is greater than every number. -/
def checkAndType : Database.Raw := strictChecked.raw.setRows 0 [{ rowid := 1, values := ["x"] }]

/-- `pair` with no list of rows for its table. -/
def unshaped : Database.Raw := { pair.raw with rows := [] }

-- The first atom that fails, in field order, and none for a valid database. `checkAndType`
-- fails two atoms, so it checks that ChecksHold comes before TypesFit.
#guard pair.raw.failingAtom? Profile.pinned == none
#guard strictChecked.raw.failingAtom? Profile.pinned == none
#guard nullInNotNull.failingAtom? Profile.pinned == some .notNull
#guard duplicateKey.failingAtom? Profile.pinned == some .keysUnique
#guard duplicateRowid.failingAtom? Profile.pinned == some .rowidsDistinct
#guard checkOnly.failingAtom? Profile.pinned == some .checksHold
#guard typeOnly.failingAtom? Profile.pinned == some .typesFit
#guard checkAndType.failingAtom? Profile.pinned == some .checksHold
#guard unshaped.failingAtom? Profile.pinned == some .rowsShaped
example : ¬nullInNotNull.Valid Profile.pinned := by
  rw [← Belay.Sqlite.Model.Database.failingAtom?_eq_none_iff]; decide +kernel

/-- Every atom, in the order of `ValidityAtom`. -/
def everyAtom : List ValidityAtom :=
  [.catalog, .rowsShaped, .rowidsDistinct, .rowidsInRange, .rowsWide, .rowsStored, .rowsAliased, .notNull,
    .checksHold, .typesFit, .keysUnique]

-- Each atom has its own name, and each name is a declaration of the model.
#guard (everyAtom.map ValidityAtom.name).eraseDups.length == 11
open Lean in
#eval show MetaM Unit from do
  for atom in everyAtom do
    unless (← getEnv).contains (`Belay.Sqlite.Model ++ atom.name.toName) do
      throwError "{atom.name} is not a declaration in Belay.Sqlite.Model; correct ValidityAtom.name"

-- The term or the error of `db!`: the error names the atom, and a valid database gives its term.
#guard match databaseTerm nullInNotNull with
  | .error message => message == invalidDatabaseMessage .notNull
  | .ok _ => false
#guard match databaseTerm pair.raw with
  | .ok term => term == databaseExpr pair.raw
  | .error _ => false
#guard invalidDatabaseMessage .notNull == "the database that db! builds is not valid: Database.NotNull does not " ++
  "hold. The model's statements keep a database valid, so this is a defect of the model; report the SQL text " ++
  "to the maintainers of the model"
