import Belay.Sqlite.Model.Output
import Belay.Sqlite.Model.Resolution.Resolve

set_option doc.verso true

/-! A run of statement syntax that continues after an error (ADR 0017, D3, amended
2026-10-22). It resolves each statement when it runs, against the state of the connection at
that time: the catalog of the visible database, the catalog at {lit}`BEGIN` of an open
transaction, and the setting of {lit}`PRAGMA foreign_keys`. It runs the statement with
{name}`Belay.Sqlite.Model.runStatement` and {name}`Belay.Sqlite.Model.advanceWith`, gives its
{name}`Belay.Sqlite.Model.Output`, and goes on with the next statement after an error, as an
application that sends one statement at a time does. A statement that the model does not
describe ends the run. {lit}`ScriptRunLaws.lean` relates the run to
{name}`Belay.Sqlite.Model.runSqlFrom`. -/

namespace Belay.Sqlite.Model

/-- The state of a connection between two statements: the visible database, the snapshot of
an open transaction and the clock assignment ({name}`SqlState`), and the setting of
{lit}`PRAGMA foreign_keys`. For example, {lean}`({ state := { database := {} } } : Connection)`
is an idle connection to the empty database with foreign keys off. -/
structure Connection where
  /-- The database, the open transaction and the clock. -/
  state : SqlState
  /-- Whether foreign keys are on; off by default, as in SQLite. -/
  foreignKeys : Bool := false

/-- The state of resolution for the next statement: the catalog of the visible database, the
catalog of the snapshot of an open transaction, and the setting. -/
def Connection.resolveState (connection : Connection) : ResolveState :=
  { catalog := connection.state.database.catalog, saved := connection.state.snapshot.map (·.catalog),
    foreignKeys := connection.foreignKeys }

/-- The connection after a statement that stopped with the outcome: an open transaction stays
open with its snapshot, as in SQLite; a failure outside a transaction, also after the rollback
of {lit}`OR ROLLBACK` ({name}`SqlState.failed`), leaves the connection idle. The database is
the outcome's. -/
def Connection.afterError (connection : Connection) (foreignKeys : Bool) : Outcome → Connection
  | .success database | .failure _ _ database =>
    { state := { connection.state with database, snapshot := none }, foreignKeys }
  | .pending persisted visible _ =>
    { state := { connection.state with database := visible, snapshot := some persisted }, foreignKeys }

/-- The reason of a statement that reads the clock, when the run has no clock. -/
def clockUnmodeled : String :=
  "the statement reads the clock, and the run has no clock; give the run a clock"

/-- What one statement of a run gives: its output and the connection after it, or the reason
why the run ends at it. -/
inductive RunStep where
  /-- The statement ran, with its output, which is not {name}`Output.unmodeled`. -/
  | continued (output : Output) (next : Connection)
  /-- The model does not describe the statement; the run ends. -/
  | ended (reason : String)

/-- Run one statement at its zero-based index on the connection:

* resolve it against {name}`Connection.resolveState`; a restriction ends the run with its reason;
* a statement that reads the clock ({name}`Resolved.Statement.readsClock`) ends the run;
* run it with {name}`runStatement`; a statement that fails the support check ends the run;
* advance the connection with {name}`advanceWith`, and give {name}`Output.ofStep`; an output
  {name}`Output.unmodeled` ends the run;
* after an error, the connection is {name}`Connection.afterError` of the outcome. -/
def runScriptStep (context : ResolveContext) (index : Nat) (connection : Connection) (statement : Syntax.Statement) :
    RunStep :=
  match resolveStatement context connection.resolveState index statement with
  | .error restriction => .ended restriction.reason
  | .ok (resolved, after) =>
    if resolved.readsClock then .ended clockUnmodeled
    else
      let clock := connection.state.clock index
      let run := runStatement clock resolved connection.state.database
      if !run.ready then .ended unmodeledHere
      else
        let transition := advanceWith index resolved connection.state run.effect
        match Output.ofStep clock resolved connection.state transition with
        | .unmodeled reason => .ended reason
        | output => .continued output (match transition with
          | .next state => { state, foreignKeys := after.foreignKeys }
          | .halt outcome => connection.afterError after.foreignKeys outcome)

/-- The result of a run: the output of each statement that ran, in order, and the connection
at the end. -/
structure ScriptRun where
  /-- One output for each statement that ran; the last is {name}`Output.unmodeled` when the
  run ended early. -/
  outputs : List Output
  /-- The connection after the last statement that ran, or at the start of the statement
  that ended the run. -/
  connection : Connection

/-- Run statements in order from a zero-based index on the connection ({name}`runScriptStep`): the
run goes on after an error and ends at a statement that the model does not describe, whose
output is {name}`Output.unmodeled`. -/
def runScriptFrom (context : ResolveContext) (index : Nat) (connection : Connection) :
    List Syntax.Statement → ScriptRun
  | [] => { outputs := [], connection }
  | statement :: rest => match runScriptStep context index connection statement with
    | .ended reason => { outputs := [.unmodeled reason], connection }
    | .continued output next =>
      let later := runScriptFrom context (index + 1) next rest
      { later with outputs := output :: later.outputs }

end Belay.Sqlite.Model
