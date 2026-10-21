import Belay.Sqlite.ForeignKeyRows
import Belay.Sqlite.UpsertRun

set_option doc.verso true

/-! The writes that check foreign keys (ADR 0018, D4): INSERT, UPDATE, DELETE and DROP TABLE
over {name}`Belay.Sqlite.runRows`, with SQLite's end of statement: a counter of violations other than zero
fails the statement as ABORT ({lit}`sqlite3VdbeCheckFkImmediate`), also after a FAIL failure,
which then keeps nothing; a ROLLBACK failure stays one. Checked natively: a FAIL failure of a
later row after a row without a parent is {lit}`FOREIGN KEY constraint failed`. -/

namespace Belay.Sqlite

/-- What a write that checks foreign keys gives: its effect, the rows that it wrote
({name}`KeyState.written`), and whether the model describes it on the database. -/
structure KeyRun where
  /-- The effect of the write. -/
  effect : Effect
  /-- The rows that the statement wrote, for its {lit}`RETURNING` rows and its change count. -/
  written : List Row
  /-- Whether the model describes the write: its rows are described ({name}`KeyStop.undescribed`
  does not occur), no subquery reads a table that an action changed, every table that an action
  changed satisfies its constraints before the write, and every changed table has bounded
  rowids. -/
  ready : Bool

/-- The end of a write that checks foreign keys over the input database: a counter other than
zero fails as ABORT, also after a FAIL failure; a FAIL failure keeps the rows that it reached,
and every other error keeps the input database. -/
def keyRun (input : Database) (target : Nat) (plain : Bool) : Except KeyStop (KeyState × Option ExecutionError) → KeyRun
  | .error .undescribed => { effect := .error (.unmodeled, input), written := [], ready := false }
  | .error (.error reason) => { effect := .error (reason, input), written := [], ready := true }
  | .ok (state, failure) =>
    let ready := (plain || state.acted.isEmpty) &&
      state.acted.all (fun position => (input.table position).all fun table =>
        LiteralData.tableReady (input.catalog.uniqueKeys position table.shape) table) &&
      (target :: state.acted).all fun position =>
        ((state.database input.catalog).rowsAt position).all (LiteralData.boundedInteger ·.rowid)
    match failure with
    | some .constraintRollback => { effect := .error (.constraintRollback, state.database input.catalog), written := [], ready }
    | some reason =>
      if state.counter != 0 then { effect := .error (.constraintViolation, input), written := [], ready }
      else { effect := .error (reason, state.database input.catalog), written := state.written, ready }
    | none =>
      if state.counter != 0 then { effect := .error (.constraintViolation, input), written := [], ready }
      else { effect := .ok (state.database input.catalog), written := state.written, ready }

/-- The algorithm of a failed constraint of an INSERT row: IGNORE skips the row, FAIL and
ROLLBACK stop the statement with their error and keep the state, and every other algorithm
fails as ABORT. -/
def failedRow (state : KeyState) : ConflictAlgorithm → Except KeyStop (KeyState × Option ExecutionError)
  | .ignore => pure (state, none)
  | .fail => pure (state, some .constraintFail)
  | .rollback => pure (state, some .constraintRollback)
  | .abort | .replace => throw (.error .constraintViolation)

/-- One row of an INSERT that checks foreign keys, as {lit}`UpsertRun` describes its constraints,
with its keys: a row that conflicts on REPLACE keys deletes the conflicting row with its foreign
keys and actions ({name}`runRows`), and more than one such row is not described; then
{name}`newSteps` checks the row, scanning the child rows only for a write of several rows; then
the row is inserted. A {lit}`DO NOTHING` clause skips the row; a {lit}`DO UPDATE` clause is
not described. The second result is a FAIL or ROLLBACK failure, which stops the statement. -/
def insertRowKeys (catalog : Catalog) (links : List ForeignKeyLink) (fuel : Nat) (target : Nat) (policy : Resolved.ConflictPolicy)
    (clauses : List Resolved.ConflictClause) (multiWrite : Bool) (state : KeyState) (values : List Value) :
    Except KeyStop (KeyState × Option ExecutionError) := do
  let some table := (state.database catalog).table target | throw .undescribed
  let keys := catalog.uniqueKeys target table.shape
  if LiteralData.aliasMismatch table.shape values then throw (.error .datatypeMismatch)
  let proposed := LiteralData.proposedRow table values
  if !LiteralData.boundedInteger proposed.rowid then throw .undescribed
  if let some column := LiteralData.nullColumn table.shape.columns proposed.values then
    return ← failedRow state (LiteralData.algorithmAt policy.notNull column)
  if !LiteralData.typesFit table.shape proposed then throw (.error .constraintViolation)
  if !LiteralData.checksHold table.shape proposed then return ← failedRow state policy.check
  if let some (clause, _) := LiteralData.handlingClause keys clauses table proposed then
    match clause.action with
    | .nothing => return (state, none)
    | .update .. => throw .undescribed
  if let some index := LiteralData.blockingKey keys policy.keys table proposed then
    return ← failedRow state (LiteralData.algorithmAt policy.keys index)
  let replaced := table.rows.filter fun row => (List.range keys.length).any fun index =>
    LiteralData.algorithmAt policy.keys index == .replace && (keys[index]?).any (LiteralData.keyEqual · row proposed)
  if replaced.length > 1 then throw .undescribed
  let state ← runRows catalog links fuel (.delete target (replaced.map (·.rowid)) false false) state
  let state ← newSteps catalog state target proposed (childLinks links target) (parentLinks links target) multiWrite none []
  let some current := (state.database catalog).table target | throw .undescribed
  match LiteralData.checkedRow keys { current with rows := current.rows ++ [proposed] } proposed with
  | .error reason => throw (.error reason)
  | .ok (next, _) =>
    return ({ state.changeRows target fun _ => next.rows with written := state.written ++ [proposed] }, none)

/-- The rows of an INSERT in order ({name}`insertRowKeys`), up to the first FAIL or ROLLBACK
failure. -/
def insertRowsKeys (catalog : Catalog) (links : List ForeignKeyLink) (fuel target : Nat) (policy : Resolved.ConflictPolicy)
    (clauses : List Resolved.ConflictClause) (multiWrite : Bool) :
    KeyState → List (List Value) → Except KeyStop (KeyState × Option ExecutionError)
  | state, [] => pure (state, none)
  | state, values :: rest => do
    match ← insertRowKeys catalog links fuel target policy clauses multiWrite state values with
    | (state, none) => insertRowsKeys catalog links fuel target policy clauses multiWrite state rest
    | (state, some reason) => pure (state, some reason)

/-- An INSERT of the rows into the table at the position that checks foreign keys, with the
trigger depth limit: a write of several rows when it has more than one row or a key whose
algorithm is REPLACE, as SQLite's {lit}`isMultiWrite` is. -/
def insertKeys (depth target : Nat) (policy : Resolved.ConflictPolicy)
    (clauses : List Resolved.ConflictClause) (rows : List (List Value)) (database : Database) (plain : Bool) : KeyRun :=
  let multiWrite := rows.length > 1 || policy.keys.contains .replace
  keyRun database target plain
    (insertRowsKeys database.catalog database.catalog.foreignKeyLinks (depth + 1) target policy clauses multiWrite
      { rows := database.rows } rows)

/-- The run of a DELETE or UPDATE work that checks foreign keys ({name}`runRows`), with the
trigger depth limit. -/
def rowsKeys (depth target : Nat) (work : RowWork) (database : Database) (plain : Bool) : KeyRun :=
  keyRun database target plain
    ((·, none) <$> runRows database.catalog database.catalog.foreignKeyLinks (depth + 1) work { rows := database.rows })

/-- An UPDATE that checks foreign keys: the rows that the filter selects, in scan order, each
with its new row as {name}`LiteralData.assign` and {name}`LiteralData.movedRowid` give it from the
row at the time SQLite writes it. -/
def updateKeys (context : Resolved.EvalContext) (depth target : Nat) (table : Table)
    (assignments : List (Nat × Resolved.Expr)) (filter : Option Resolved.Expr) (database : Database) (plain : Bool) :
    KeyRun :=
  let rowids := (table.scanRows.filter (LiteralData.selected context filter)).map (·.rowid)
  let change (row : Row) := LiteralData.movedRowid table.shape.rowidAlias
    (LiteralData.assign context table.shape.columns assignments row)
  rowsKeys depth target (.update target change (table.shape.changedColumns (assignments.map (·.1))) rowids true)
    database plain

/-- A DELETE that checks foreign keys: the rows that the filter selects, in scan order. -/
def deleteKeys (context : Resolved.EvalContext) (depth target : Nat) (table : Table)
    (filter : Option Resolved.Expr) (database : Database) (plain : Bool) : KeyRun :=
  let rowids := (table.scanRows.filter (LiteralData.selected context filter)).map (·.rowid)
  rowsKeys depth target (.delete target rowids true false) database plain

/-- DROP TABLE of a table that foreign keys reference: SQLite first deletes every row of the
table with {lit}`disableTriggers` ({name}`oldSteps` with {lit}`ignore`), then fails when the counter
is not zero and otherwise removes the objects at the positions from the database after the
DELETE. -/
def dropKeys (depth : Nat) (positions : List Nat) (database : Database) : KeyRun :=
  match positions, positions.head?.bind database.table with
  | target :: _, some table =>
    let run := rowsKeys depth target (.delete target (table.scanRows.map (·.rowid)) false true) database true
    match run.effect with
    | .ok after => { run with effect := .ok (after.drop positions) }
    | .error _ => run
  | _, _ => { effect := .ok (database.drop positions), written := [], ready := true }

/-- For every input database, table, flag, result and database: if the run ({name}`keyRun`)
succeeds with the database, the database has the input's catalog. Proof sketch: the success is
the state's rows over the input catalog ({name}`KeyState.database`). -/
theorem keyRun_ok_catalog {input result : Database} {target : Nat} {plain : Bool}
    {outcome : Except KeyStop (KeyState × Option ExecutionError)}
    (ok : (keyRun input target plain outcome).effect = .ok result) : result.catalog = input.catalog := by
  unfold keyRun at ok
  repeat' split at ok
  all_goals first | (cases ok; rfl) | cases ok

/-- For every database, positions, depth and result: if DROP TABLE with foreign keys
({name}`dropKeys`) succeeds, the result's catalog is the input catalog without the objects at the
positions, as for the plain DROP. Proof sketch: the DELETE keeps the catalog
({name}`keyRun_ok_catalog`) and {name}`Database.drop` removes the objects. -/
theorem dropKeys_ok_catalog {database result : Database} {depth : Nat} {positions : List Nat}
    (ok : (dropKeys depth positions database).effect = .ok result) :
    result.catalog = database.catalog.drop positions := by
  unfold dropKeys at ok
  split at ok
  · simp only [] at ok
    split at ok
    · rename_i after deleted
      cases ok
      simp only [Database.drop, keyRun_ok_catalog deleted]
    · rename_i failed
      rw [failed] at ok
      cases ok
  · cases ok; rfl

end Belay.Sqlite
