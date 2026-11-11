import Belay.Sqlite.Model.Shared.Execution.SqlExecution

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- A row that a statement returns: its cells, with their storage classes and exact payloads. -/
abbrev ResultRow := List Value

/-- What a statement that runs returns. For example, a successful
{lit}`UPDATE t SET a = 1` that changes two rows gives {lean}`({ columns := [], rows := [], changes := some 2 } : StatementOutput)`. -/
structure StatementOutput where
  /-- The names of the result columns, also when no row comes back. -/
  columns : List String
  /-- The rows, in the order that {lit}`statementOutput` describes. -/
  rows : List ResultRow
  /-- The number of rows that a write changed: present for INSERT, UPDATE and DELETE, and
  absent for every other statement. -/
  changes : Option Nat
  deriving Repr, DecidableEq

/-- SQLite's primary result code of a statement error ({lit}`SQLITE_CONSTRAINT` 19,
{lit}`SQLITE_MISMATCH` 20, and {lit}`SQLITE_ERROR` 1 for every other modeled error). For
example, {lean}`ExecutionError.constraintViolation.primaryCode` is 19. -/
def ExecutionError.primaryCode : ExecutionError → Nat
  | .constraintViolation | .constraintFail | .constraintRollback => 19
  | .datatypeMismatch => 20
  | .unmodeled | .prepare _ | .transactionAlreadyActive | .noActiveTransaction | .integerOverflow | .functionError
  | .nullColumnDefault | .nonConstantColumnDefault | .checkColumnDefault | .referenceColumnDefault => 1

/-- The error with which a transition stops: the reason of a failure, or the error of a
pending transaction; none for a transition that continues or succeeds. -/
def haltError : SqlTransition → Option ExecutionError
  | .next _ | .halt (.success _) => none
  | .halt (.failure _ reason _) => some reason
  | .halt (.pending _ _ error) => error.map (·.2)

/-- Whether an execution error is a failed write, whose outputs are the {lit}`RETURNING`
names, no rows and no change: a constraint failure or a datatype mismatch, which for a write is
a rowid alias mismatch. -/
def ExecutionError.failsWrite : ExecutionError → Bool
  | .constraintViolation | .constraintFail | .constraintRollback | .datatypeMismatch => true
  | .unmodeled | .prepare _ | .transactionAlreadyActive | .noActiveTransaction | .integerOverflow
  | .functionError | .nullColumnDefault | .nonConstantColumnDefault | .checkColumnDefault
  | .referenceColumnDefault => false

end Belay.Sqlite.Model
