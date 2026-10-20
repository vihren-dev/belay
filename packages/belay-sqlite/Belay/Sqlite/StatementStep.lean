import Belay.Sqlite.SqlState
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

/-- The unique keys of the table at the position in the database's catalog
({name}`Catalog.uniqueKeys`), which every write to it keeps unique. -/
def Database.keys (database : Database) (target : Nat) (table : Table) : List UniqueKey :=
  database.catalog.uniqueKeys target table.shape

/-- Store a write's result when it satisfies the constraints of the given keys and its
rowids are distinct ({name}`LiteralData.rowidsDistinct`), or fail with
{lean}`ExecutionError.constraintViolation` and the input database. -/
def checkedWrite (database : Database) (target : Nat) (keys : List UniqueKey) (result : Table) : Effect :=
  if LiteralData.constraints keys result && LiteralData.rowidsDistinct result then
    .ok (database.setRows target result.rows)
  else .error (.constraintViolation, database)

/-- The outcome of INSERT: SQLite inserts the rows in order, and refuses a rowid alias
that is not an integer before the constraints of its row
({name}`LiteralData.aliasMismatch`), so the first such row is
{lean}`ExecutionError.datatypeMismatch` unless the rows before it already fail; with no
such row, {name}`checkedWrite` of the table with all rows inserted ({lit}`result`, which is
{name}`LiteralData.inserted`). A failure keeps the input database. -/
def insertOutcome (database : Database) (target : Nat) (keys : List UniqueKey) (table : Table)
    (rows : List (List Value)) (result : Table) : Effect :=
  match rows.findIdx? (LiteralData.aliasMismatch table.shape) with
  | some index =>
    let before := LiteralData.inserted table (rows.take index)
    if LiteralData.constraints keys before && LiteralData.rowidsDistinct before then
      .error (.datatypeMismatch, database)
    else .error (.constraintViolation, database)
  | none => checkedWrite database target keys result

/-- What running one statement on a database gives: its effect, and whether the model
describes it on the database (the support check). Both read the same computation of the
write or the query. -/
structure StatementRun where
  /-- The effect of the statement ({lit}`literalStep`). -/
  effect : Effect
  /-- Whether the model describes the statement on the database ({lit}`statementReady`). -/
  ready : Bool

/-- Run one statement at a clock value, computing each write and query once for its
effect and its support check (ADR 0013, D8). The effect: INSERT and UPDATE with ABORT
constraints over the table's keys ({name}`Database.keys`), INSERT with {lit}`ON CONFLICT`
clauses or algorithms row by row ({name}`LiteralData.upsertSteps`), each over the rows at
the clock value ({name}`Resolved.rowsAt`), in the plain context of the clock value
({name}`Resolved.EvalContext.plain`), DELETE, which removes rows and cannot fail a
constraint, a query ({name}`queryEffect`), and {name}`step` for every other statement. A
position without a table fails as {lean}`ExecutionError.unmodeled`. An error carries the
database that the statement reached: the rows before the failing row of an INSERT with
clauses or algorithms, and the input database for every other error. The support check:
INSERT and UPDATE pass the data domain of the table, every write and query the JSON
checks of {lit}`JsonReady`, and a query's subqueries have no fallible call
({name}`Resolved.Expr.isFallibleCall`), because SQLite may evaluate a subquery for rows that the
model does not reach; a position without a table passes and fails during execution
instead. ADD COLUMN must have modeled default readback, a model restriction, because SQLite
accepts such statements. CREATE TABLE passes, as its table has no rows to violate a
constraint (ADR 0014, slice 4), and so do CREATE INDEX and the other statement forms. -/
def runStatement (clock : Int) (statement : Resolved.Statement) (database : Database) : StatementRun :=
  let context := Resolved.EvalContext.plain clock
  match statement with
  | .insert target rows returning => match database.table target with
    | none => { effect := .error (.unmodeled, database), ready := true }
    | some table =>
      let keys := database.keys target table
      let values := Resolved.rowsAt context table.shape.columns rows
      let result := LiteralData.inserted table values
      { effect := insertOutcome database target keys table values result,
        ready := LiteralData.insertReady keys table values result &&
          !(returningExpressions returning).any (·.any Resolved.Expr.isFallibleCall) }
  | .upsert target rows clauses returning algorithm => match database.table target with
    | none => { effect := .error (.unmodeled, database), ready := true }
    | some table =>
      let keys := database.keys target table
      let policy := database.catalog.writePolicy target table.shape algorithm
      let values := Resolved.rowsAt context table.shape.columns rows
      let steps := LiteralData.upsertSteps context keys policy clauses table values
      { effect := match LiteralData.upsertSummary table steps with
          | .ok (result, _) => .ok (database.setRows target result.rows)
          | .error (reason, reached, _) => .error (reason, database.setRows target reached.rows),
        ready := LiteralData.upsertReady keys table clauses values steps && upsertJsonReady clauses returning }
  | .update target assignments filter returning => match database.table target with
    | none => { effect := .error (.unmodeled, database), ready := true }
    | some table =>
      let keys := database.keys target table
      let result := LiteralData.updated context table assignments filter
      { effect := if LiteralData.updateMismatch context table assignments filter then .error (.datatypeMismatch, database)
          else checkedWrite database target keys result,
        ready := LiteralData.updateReady keys table assignments result &&
          updateJsonReady context table assignments filter returning }
  | .delete target filter returning => match database.table target with
    | none => { effect := .error (.unmodeled, database), ready := true }
    | some table =>
      { effect := .ok (database.setRows target (LiteralData.deleted context table filter).rows),
        ready := deleteJsonReady context table filter returning }
  | .query query subqueries =>
    let ran := query.runOn clock database subqueries
    { effect := queryEffect database ran,
      ready := subqueries.all (·.expressions.all (!·.any Resolved.Expr.isFallibleCall)) &&
        ran.all fun (source, run) => source.fault != .may && run.fault != .may }
  | .createTable .. => { effect := step clock statement database, ready := true }
  | .addColumn _ column =>
    { effect := step clock statement database,
      ready := column.clockDefault || (readDefaultValue column).toOption.isSome }
  | .createIndex .. | .drop _ => { effect := step clock statement database, ready := true }
  | .begin | .commit | .rollback | .prepareError _ => { effect := step clock statement database, ready := true }

/-- The effect of one statement at a clock value ({name}`runStatement`). This computation
does not establish the separate stored-value support obligation. -/
def literalStep (clock : Int) (statement : Resolved.Statement) (database : Database) : Effect :=
  (runStatement clock statement database).effect

/-- Whether the model describes the statement on the database ({name}`runStatement`). Use
it through the reached-statement script support check. -/
def statementReady (clock : Int) (statement : Resolved.Statement) (database : Database) : Bool :=
  (runStatement clock statement database).ready

/-- One statement at its supplied zero-based position with its effect. BEGIN records a
snapshot; COMMIT clears it; ROLLBACK restores it. Repeated BEGIN or transaction
closure without a snapshot halts with an error. Other statements use
the effect, which {lit}`advance` computes at the clock value of the position
({name}`SqlState.clock`); an error retains any open transaction, except a ROLLBACK failure,
which rolls it back ({name}`SqlState.failed`). -/
def advanceWith (position : Nat) (statement : Resolved.Statement) (state : SqlState) (effect : Effect) :
    SqlTransition :=
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
  | .createTable .. | .createIndex .. | .addColumn .. | .drop _ | .insert .. | .upsert .. | .update .. | .delete ..
  | .prepareError _ | .query .. =>
    state.publish position effect

/-- Evaluate one statement at its supplied zero-based position ({name}`advanceWith` of its
effect at the clock value of the position, {name}`literalStep`). -/
def advance (position : Nat) (statement : Resolved.Statement) (state : SqlState) : SqlTransition :=
  advanceWith position statement state (literalStep (state.clock position) statement state.database)

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
transition, both from one run of the statement ({name}`runStatement`). After a halt,
unreachable statements impose no obligation. An empty script passes. -/
def supportedSqlFrom (position : Nat) (script : List Resolved.Statement) (state : SqlState) : Bool :=
  match script with
  | [] => true
  | statement :: rest =>
    let run := runStatement (state.clock position) statement state.database
    run.ready &&
    match advanceWith position statement state run.effect with
    | .halt _ => true
    | .next next => supportedSqlFrom (position + 1) rest next

end Belay.Sqlite
