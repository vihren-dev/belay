import Belay.Sqlite.Model
import Belay.Sqlite.Resolution.Resolved

set_option doc.verso true

/-! Errors, outcomes and the definition steps of the execution semantics, which
runs resolved statements. Resource failures and crashes are outside this model. -/

namespace Belay.Sqlite

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
  /-- A literal write violates a NOT NULL or unique-key constraint. -/
  | constraintViolation
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

/-- Whether the model runs a definition of this column: no NOT NULL and no default. -/
def CatalogColumn.plain (column : CatalogColumn) : Bool := !column.notNull && column.defaultValue.isNone

/-- Whether the model runs a CREATE TABLE of this table: plain columns, no keys and
no rowid alias. {lit}`resolve` refuses other tables in statements that run. -/
def CatalogTable.plain (table : CatalogTable) : Bool :=
  table.columns.all CatalogColumn.plain && table.primaryKey.isEmpty && table.uniqueKeys.isEmpty &&
    table.rowidAlias.isNone

/-- Perform CREATE TABLE or ADD COLUMN at the supplied position, or fail with the
prepare error of a statement that SQLite refuses. CREATE TABLE stores an empty
table at its catalog position; ADD COLUMN appends NULL to each existing row.
Other constructors, and a definition outside the modeled subset, fail with
{lean}`ExecutionError.unmodeled`; SQL execution handles transaction control and
writes separately. The default position is zero. -/
def step (statement : Resolved.Statement) (database : Database) (position : Nat := 0) : Outcome :=
  match statement with
  | .createTable at_ _ table =>
    if !table.plain then .failure position .unmodeled database
    else match database at_ with
      | some _ => .failure position .unmodeled database
      | none => .success (database.set at_ { shape := table, rows := [] })
  | .addColumn at_ column =>
    if !column.plain then .failure position .unmodeled database
    else match database at_ with
      | none => .failure position .unmodeled database
      | some table => .success (database.set at_ (table.appendColumns [column]))
  | .prepareError error => .failure position (.prepare error) database
  | .createIndex .. | .begin | .commit | .rollback | .insert .. | .update .. =>
    .failure position .unmodeled database

end Belay.Sqlite
