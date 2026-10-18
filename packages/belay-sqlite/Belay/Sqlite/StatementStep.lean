import Belay.Sqlite.Execution
import Belay.Sqlite.RowDelete
import Belay.Sqlite.UpsertRun
import Belay.Sqlite.JsonReady
import Belay.Sqlite.StatementClock

set_option doc.verso true

/-! The steps of script-directed SQL execution of resolved statements. Each statement runs
at the clock value that the state's clock assignment gives for its position;
{lit}`SqlExecution.lean` chooses the assignment. BEGIN records the
committed snapshot; an explicit COMMIT/ROLLBACK, or an INSERT that fails with the
ROLLBACK algorithm, changes transaction state. Other statement errors stop execution
without inferring connection closure, framework cleanup, or transaction rollback. -/
namespace Belay.Sqlite

/-- The current connection view, optional transaction snapshot and clock assignment.
Supply a database and omit the snapshot for an idle connection. -/
structure SqlState where
  /-- Current connection-visible storage. -/
  database : Database
  /-- Pre-BEGIN committed storage; omit it outside a transaction. -/
  snapshot : Option Database := none
  /-- The clock value of the statement at each zero-based position, in SQLite's Julian-day
  milliseconds; 0 at every position by default, for a script that reads no clock. -/
  clock : Nat → Int := fun _ => 0

/-- Attach an open transaction to a terminal result. A success becomes pending
without an error; a failure becomes pending with its position/error. An existing
pending result is retained. With no snapshot, return the supplied outcome. -/
def SqlState.finish (state : SqlState) (outcome : Outcome) : Outcome :=
  match state.snapshot, outcome with
  | none, _ => outcome
  | some original, .success result => .pending original result none
  | some original, .failure index reason result => .pending original result (some (index, reason))
  | _, .pending .. => outcome

/-- The outcome of a statement that fails: a ROLLBACK failure in an open transaction
rolls it back, so it is the failure over the snapshot outside a transaction; every other
failure, and a ROLLBACK failure without a transaction, is {name}`SqlState.finish` of the
failure. -/
def SqlState.failed (state : SqlState) (position : Nat) (reason : ExecutionError) (database : Database) : Outcome :=
  if reason = .constraintRollback then match state.snapshot with
    | some original => .failure position reason original
    | none => state.finish (.failure position reason database)
  else state.finish (.failure position reason database)

/-- One SQL transition either continues with a connection state or halts with an
{name}`Outcome`. Evaluate a supplied statement to obtain a transition. -/
inductive SqlTransition where
  /-- Continue with this updated connection state. -/
  | next (state : SqlState)
  /-- Stop with this error or terminal result. -/
  | halt (outcome : Outcome)

/-- The transition of a statement's effect at its position, the one path that publishes
the result of a statement (ADR 0013, D8): an effect that succeeds continues with its
database; an error halts with the database that its algorithm keeps: the database that a
FAIL failure reached ({lean}`ExecutionError.constraintFail`), which keeps the earlier rows,
the input database for every other error, and the snapshot for ROLLBACK in a transaction
({name}`SqlState.failed`). -/
def SqlState.publish (state : SqlState) (position : Nat) : Effect → SqlTransition
  | .ok database => .next { state with database }
  | .error (reason, reached) =>
    .halt (state.failed position reason (if reason = .constraintFail then reached else state.database))

/-- The unique keys of the table at the position in the database's catalog
({name}`Catalog.uniqueKeys`), which every write to it keeps unique. -/
def Database.keys (database : Database) (target : Nat) (table : Table) : List (List Nat) :=
  database.catalog.uniqueKeys target table.shape

/-- Store a write's result when it satisfies the constraints of the given keys and its
rowids are distinct ({name}`LiteralData.rowidsDistinct`), or fail with
{lean}`ExecutionError.constraintViolation` and the input database. -/
def checkedWrite (database : Database) (target : Nat) (keys : List (List Nat)) (result : Table) : Effect :=
  if LiteralData.constraints keys result && LiteralData.rowidsDistinct result then
    .ok (database.setRows target result.rows)
  else .error (.constraintViolation, database)

/-- The outcome of INSERT: SQLite inserts the rows in order, and refuses a rowid alias
that is not an integer before the constraints of its row
({name}`LiteralData.aliasMismatch`), so the first such row is
{lean}`ExecutionError.datatypeMismatch` unless the rows before it already fail; with no
such row, {name}`checkedWrite` of all rows. A failure keeps the input database. -/
def insertOutcome (database : Database) (target : Nat) (keys : List (List Nat)) (table : Table)
    (rows : List (List Value)) : Effect :=
  match rows.findIdx? (LiteralData.aliasMismatch table.shape) with
  | some index =>
    let before := LiteralData.inserted table (rows.take index)
    if LiteralData.constraints keys before && LiteralData.rowidsDistinct before then
      .error (.datatypeMismatch, database)
    else .error (.constraintViolation, database)
  | none => checkedWrite database target keys (LiteralData.inserted table rows)

/-- Apply INSERT/UPDATE with ABORT constraints over the table's keys
({name}`Database.keys`), INSERT with
{lit}`ON CONFLICT` clauses row by row ({name}`LiteralData.upsertRun`), each over the rows
at the clock value ({name}`Resolved.rowsAt`), and DELETE,
which removes rows and cannot fail a constraint. A position without a table fails as
{lean}`ExecutionError.unmodeled`. An error carries the database that the statement
reached: the rows before the failing row of an INSERT with clauses or algorithms, and the
input database for every other error. Other statements use {name}`step`. This
computation does not establish the separate stored-value support obligation. -/
def literalStep (clock : Int) (statement : Resolved.Statement) (database : Database) : Effect :=
  match statement with
  | .insert target rows _ => match database.table target with
    | none => .error (.unmodeled, database)
    | some table =>
      insertOutcome database target (database.keys target table) table (Resolved.rowsAt clock table.shape.columns rows)
  | .upsert target rows clauses _ algorithm => match database.table target with
    | none => .error (.unmodeled, database)
    | some table =>
      let policy := database.catalog.writePolicy target table.shape algorithm
      match LiteralData.upsertRun clock (database.keys target table) policy clauses table
          (Resolved.rowsAt clock table.shape.columns rows) with
      | .ok (result, _) => .ok (database.setRows target result.rows)
      | .error (reason, reached, _) => .error (reason, database.setRows target reached.rows)
  | .update target assignments filter _ => match database.table target with
    | none => .error (.unmodeled, database)
    | some table =>
      if LiteralData.updateMismatch clock table assignments filter then .error (.datatypeMismatch, database)
      else checkedWrite database target (database.keys target table) (LiteralData.updated clock table assignments filter)
  | .delete target filter _ => match database.table target with
    | none => .error (.unmodeled, database)
    | some table => .ok (database.setRows target (LiteralData.deleted clock table filter).rows)
  | .createTable .. | .createIndex .. | .addColumn .. | .begin | .commit | .rollback | .prepareError _ | .query _ =>
    step clock statement database

/-- Check that the model describes the statement against the current table.
INSERT/UPDATE must pass the data domain of the table, and every write and query the
JSON checks of {lit}`JsonReady` at the statement's clock value; a position without a table
passes and fails during execution instead. CREATE TABLE must be plain; ADD COLUMN must have modeled default
readback; CREATE INDEX fails: these are model restrictions, because SQLite accepts such
statements. Other statement forms pass. Use it through the reached-statement script
support check. -/
def statementReady (clock : Int) (statement : Resolved.Statement) (database : Database) : Bool :=
  match statement with
  | .insert target rows returning => (database.table target).all fun table =>
      LiteralData.insertReady (database.keys target table) table (Resolved.rowsAt clock table.shape.columns rows) &&
        !(returningExpressions returning).any (·.any Resolved.Expr.isJsonCall)
  | .upsert target rows clauses returning algorithm => (database.table target).all fun table =>
      LiteralData.upsertReady clock (database.keys target table) (database.catalog.writePolicy target table.shape algorithm)
        table clauses (Resolved.rowsAt clock table.shape.columns rows) && upsertJsonReady clauses returning
  | .update target assignments filter returning => (database.table target).all fun table =>
      LiteralData.updateReady clock (database.keys target table) table assignments filter &&
        updateJsonReady clock table assignments filter returning
  | .delete target filter returning => (database.table target).all fun table => deleteJsonReady clock table filter returning
  | .createTable _ _ table => table.plain
  | .addColumn _ column => column.clockDefault || (readDefaultValue column).toOption.isSome
  | .createIndex .. => false
  | .query query =>
    (query.source clock database).all fun source => source.fault != .may && (query.run clock source.rows).fault != .may
  | .begin | .commit | .rollback | .prepareError _ => true

/-- Evaluate one statement at its supplied zero-based position. BEGIN records a
snapshot; COMMIT clears it; ROLLBACK restores it. Repeated BEGIN or transaction
closure without a snapshot halts with an error. Other statements use
{name}`literalStep` at the clock value of the position ({name}`SqlState.clock`); an error retains any open transaction, except a ROLLBACK failure,
which rolls it back ({name}`SqlState.failed`). -/
def advance (position : Nat) (statement : Resolved.Statement) (state : SqlState) : SqlTransition :=
  match statement with
  | .begin => match state.snapshot with
    | some _ => .halt (state.finish (.failure position .transactionAlreadyActive state.database))
    | none => .next { state with snapshot := some state.database }
  | .commit => match state.snapshot with
    | none => .halt (.failure position .noActiveTransaction state.database)
    | some _ => .next { state with snapshot := none }
  | .rollback => match state.snapshot with
    | none => .halt (.failure position .noActiveTransaction state.database)
    | some original => .next { state with database := original, snapshot := none }
  | .createTable .. | .createIndex .. | .addColumn .. | .insert .. | .upsert .. | .update .. | .delete ..
  | .prepareError _ | .query _ =>
    state.publish position (literalStep (state.clock position) statement state.database)

/-- Execute the script from a supplied position and connection state. A halt stops
the script; a continuing transition advances the position. EOF finishes the
current state and preserves an open transaction. The idle wrapper starts at position zero. -/
def runSqlFrom (position : Nat) (script : List Resolved.Statement) (state : SqlState) : Outcome :=
  match script with
  | [] => state.finish (.success state.database)
  | statement :: rest => match advance position statement state with
    | .halt outcome => outcome
    | .next next => runSqlFrom (position + 1) rest next

/-- Execute a resolved script from position zero outside a transaction. Use
{name}`runSqlFrom` for an explicit position/state. A file is not implicitly atomic;
transaction control must be supplied in its statements. -/
def runSql (script : List Resolved.Statement) (database : Database) : Outcome :=
  runSqlFrom 0 script { database := database }

/-- Check {name}`statementReady` at every reached statement and follow the actual
transition. After a halt, unreachable statements impose no obligation. An empty
script passes. -/
def supportedSqlFrom (position : Nat) (script : List Resolved.Statement) (state : SqlState) : Bool :=
  match script with
  | [] => true
  | statement :: rest =>
    let clock := state.clock position
    statementReady clock statement state.database &&
    match advance position statement state with
    | .halt _ => true
    | .next next => supportedSqlFrom (position + 1) rest next

end Belay.Sqlite
