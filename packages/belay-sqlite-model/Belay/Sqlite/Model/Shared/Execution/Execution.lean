import Belay.Sqlite.Model.Shared.Catalog.Database
import Belay.Sqlite.Model.Shared.Resolved.Resolved

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- A modeled statement error. For example, {lean}`ExecutionError.noActiveTransaction`
reports COMMIT or ROLLBACK without an open transaction. -/
inductive ExecutionError where
  /-- The execution semantics does not model this statement against this database:
  a definition outside the modeled subset, or a write to a position without a
  table. {lit}`resolve` gives no such statement for a conforming database. -/
  | unmodeled
  /-- SQLite refused to prepare the statement; resolution decided the error. -/
  | prepare (error : PrepareError)
  /-- BEGIN encounters an open transaction. -/
  | transactionAlreadyActive
  /-- COMMIT or ROLLBACK encounters no open transaction. -/
  | noActiveTransaction
  /-- A literal write violates a NOT NULL or unique-key constraint, with ABORT: the
  statement's changes are undone. -/
  | constraintViolation
  /-- A row of INSERT violates a NOT NULL or unique-key constraint with FAIL: the
  statement stops and keeps the changes of its earlier rows. -/
  | constraintFail
  /-- A row of INSERT violates a NOT NULL or unique-key constraint with ROLLBACK: the
  statement fails and the open transaction is rolled back. -/
  | constraintRollback
  /-- A query's {lit}`SUM` overflows the 64-bit integers: SQLite's {lit}`integer overflow`,
  reported while the statement runs. -/
  | integerOverflow
  /-- A value for a rowid alias that is not an integer after INTEGER affinity, a NULL
  assigned to it by UPDATE, or a value bound to {lit}`LIMIT ?` or {lit}`OFFSET ?` of a query that
  is not an integer ({lit}`Query.bindWindow`): SQLite's {lit}`datatype mismatch`
  ({lit}`SQLITE_MISMATCH`), reported while the statement runs. -/
  | datatypeMismatch
  /-- A JSON function of a query fails: SQLite's {lit}`malformed JSON` or
  {lit}`bad JSON path`, reported while the statement runs. -/
  | functionError
  /-- ADD COLUMN would give existing rows NULL in a NOT NULL column: primary code 1, while the
  statement runs; an empty table permits the addition. -/
  | nullColumnDefault
  /-- ADD COLUMN with a time default ({lit}`CatalogColumn.clockDefault`) on a table with
  rows: SQLite's {lit}`Cannot add a column with non-constant default`, reported while the
  statement runs with primary code 1; an empty table permits the addition. -/
  | nonConstantColumnDefault
  /-- ADD COLUMN whose CHECK constraint an existing row with the new column's default fails:
  SQLite's {lit}`CHECK constraint failed`, with primary code 1 while the statement runs, not as a
  constraint error; an empty table permits the addition (ADR 0014, slice 4). -/
  | checkColumnDefault
  /-- ADD COLUMN of a {lit}`REFERENCES` column with a default other than a literal NULL, foreign
  keys on, on a table with rows: SQLite's {lit}`Cannot add a REFERENCES column with non-NULL
  default value`, with primary code 1, even when a parent row matches. An empty table permits it. -/
  | referenceColumnDefault
  deriving Repr, DecidableEq

/-- The final database and transaction status. Use {lean}`Outcome.success`
for successful execution outside a transaction. -/
inductive Outcome where
  /-- Successful computation with its resulting database. The SQL executor uses
  a pending outcome when a transaction remains open. -/
  | success (database : Database)
  /-- A stopped statement at its zero-based position, with the resulting database. -/
  | failure (position : Nat) (reason : ExecutionError) (database : Database)
  /-- An open transaction's original storage, visible database and optional error. -/
  | pending (persisted visible : Database) (error : Option (Nat × ExecutionError))

/-- What one statement does to the database, without its position (ADR 0006): the
database after it, or the error with the database that the statement reached, which
the script decides to keep or not ({lit}`SqlState.publish`). For example, a FAIL failure
of an INSERT reaches the database with its earlier rows. -/
abbrev Effect := Except (ExecutionError × Database) Database

/-- The database of an effect: the database after it, or the database that its error
reached. -/
def effectDatabase : Effect → Database
  | .ok database => database
  | .error (_, database) => database

/-- Read the resulting visible database from every outcome, including an open
transaction. A separate accessor reads committed storage. -/
def Outcome.database : Outcome → Database
  | .success database | .failure _ _ database => database
  | .pending _ visible _ => visible

/-- Read the committed database: an open transaction exposes its original snapshot;
otherwise this is the visible {name}`Outcome.database`. -/
def Outcome.persistedDatabase : Outcome → Database
  | .pending persisted _ _ => persisted
  | outcome => outcome.database

end Belay.Sqlite.Model
