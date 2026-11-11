import Belay.Sqlite.Model.Programs.Clock.SqlExecution
import Belay.Sqlite.Model.Schema.Columns.StatementOutput
import Belay.Sqlite.Model.Shared.Execution.StatementOutput

set_option doc.verso true

/-! The output of each statement that runs: its result column names, its rows and its number of
changes, computed from the statement's transition, without a second evaluator; and SQLite's
primary result code of a statement error. The conformance harness compares these outputs with
native SQLite (ADR 0005), and the user surface shows them (ADR 0017, D3). -/

namespace Belay.Sqlite.Model

/-- The {lit}`RETURNING` rows of a write: each {lit}`RETURNING` expression evaluated over
each written row in the statement's evaluation context, in order. A write without
{lit}`RETURNING` returns no rows. -/
def returnedRows (context : Resolved.EvalContext) (returning : List (Resolved.Expr × String)) (written : List (List Value)) :
    List ResultRow :=
  if returning.isEmpty then [] else written.map fun row => returning.map fun (expression, _) => expression.eval context row

/-- Observe the literal-DML domain of a statement with the values bound to its parameters;
unsupported output capability is explicit.
Transitions and failure status come from production advance, never a second
evaluator. The change count of a write is {lit}`changes` of the counts of its run
({name}`StatementRun.counts`), which the run of the statement computed together with its effect
(ADR 0024, D2): a successful INSERT changes one row per VALUES row and a successful
UPDATE changes each row that its filter selects; their {lit}`RETURNING` rows are
{name}`returnedRows` of the cells of the inserted rows (with the rowid of a NULL rowid
alias), or of the new values of the selected rows. A successful INSERT with
{lit}`ON CONFLICT` clauses changes each row that it inserted or updated, and its
{lit}`RETURNING` rows are {name}`returnedRows` of those rows in row order
({name}`LiteralData.upsertRun`); skipped and deleted rows are not counted, and a FAIL
failure counts the rows before the failing one. A
successful DELETE changes each row that its filter selects, and its {lit}`RETURNING` rows
are {name}`returnedRows` of the old values of those rows. UPDATE and DELETE return their
rows in scan order ({name}`Belay.Sqlite.Model.Table.scanRows`): rowid order, or key order for a
{lit}`WITHOUT ROWID` table. A write that fails a
constraint or a rowid alias ({lit}`datatype mismatch`) returns its {lit}`RETURNING` names
and no rows. A query has its result column
names and the rows of {name}`Resolved.Query.run` over the table before it, and no
change count; a query whose table is missing has no output. A query that fails with
{lit}`integer overflow` has its column names and no rows when it has no
{lit}`GROUP BY`; with {lit}`GROUP BY`, SQLite may return the rows of other groups
before the failing one, in an order the model does not describe, so it has no output. A
query whose JSON function fails, which has no {lit}`FROM` and so at most one row, has its
column names and no rows, and so has a query that fails with {lit}`datatype mismatch` because a
value of its window is not an integer, which SQLite reads before the first row. A write that
checks foreign keys (ADR 0018, D4) has the rows that its keys' run wrote
({name}`StatementRun.keyRows`) and the counts of its run: its {lit}`RETURNING` rows and change count
when it succeeds, and its {lit}`RETURNING` names, no rows and the rows that a FAIL failure kept when
it fails a constraint. An INSERT from a query, which keeps the same outputs, also has them when it
fails with {lit}`integer overflow` or a function error while it reads its source: its {lit}`RETURNING` names,
no rows and the changes of its run. A setting pragma ({lit}`PRAGMA setting = value`) has no output columns. -/
def statementOutput (clock : Int) (parameters : List Value) (statement : Resolved.Statement) (before : SqlState)
    (run : StatementRun) (transition : SqlTransition) : Option StatementOutput :=
  let counters := before.counters.view statement.counterReads
  let successful := match transition with | .next _ => true | .halt _ => false
  let constraintFailure := (haltError transition).any ExecutionError.failsWrite
  let overflow := haltError transition == some .integerOverflow
  let functionFailure := haltError transition == some .functionError
  let mismatch := haltError transition == some .datatypeMismatch
  match statement with
  | .insert target rows returning subqueries none =>
    let context := Resolved.statementContext clock counters parameters before.database subqueries
    let names := returning.map (·.2)
    if successful then do
      let table ← before.database.table target
      let values := Resolved.rowsAt context table.shape.columns rows
      let written := ((LiteralData.inserted table values).rows.drop table.rows.length).map (·.values)
      return ⟨names, returnedRows context returning written, some (run.counts.changes.getD 0)⟩
    else if constraintFailure then some ⟨names, [], some (run.counts.changes.getD 0)⟩ else none
  | .upsert target rows clauses returning algorithm subqueries none =>
    let context := Resolved.statementContext clock counters parameters before.database subqueries
    let names := returning.map (·.2)
    let rows := (before.database.table target).map fun table =>
      LiteralData.upsertRun context (before.database.keys target table)
        (before.database.catalog.writePolicy target table.shape algorithm) clauses table
        (Resolved.rowsAt context table.shape.columns rows)
    if successful then do
      let (_, written) ← (← rows).toOption
      return ⟨names, returnedRows context returning (written.map (·.values)), some (run.counts.changes.getD 0)⟩
    else if constraintFailure then some ⟨names, [], some (run.counts.changes.getD 0)⟩ else none
  | .update target assignments filter returning subqueries none =>
    let context := Resolved.statementContext clock counters parameters before.database subqueries
    let names := returning.map (·.2)
    if successful then do
      let table ← before.database.table target
      let chosen := table.scanRows.filter (LiteralData.selected context filter)
      let written := chosen.map fun row => (LiteralData.assign context table.shape.columns assignments row).values
      return ⟨names, returnedRows context returning written, some (run.counts.changes.getD 0)⟩
    else if constraintFailure then some ⟨names, [], some (run.counts.changes.getD 0)⟩ else none
  | .delete target filter returning subqueries none =>
    let context := Resolved.statementContext clock counters parameters before.database subqueries
    let names := returning.map (·.2)
    if successful then do
      let table ← before.database.table target
      let chosen := table.scanRows.filter (LiteralData.selected context filter)
      return ⟨names, returnedRows context returning (chosen.map (·.values)), some (run.counts.changes.getD 0)⟩
    else none
  | .query query subqueries =>
    let context := Resolved.statementContext clock counters parameters before.database subqueries
    if successful then
      (query.source context before.database).map fun source => ⟨query.names, (query.run context source.rows).rows, none⟩
    else if (overflow && query.groupBy.isEmpty) || functionFailure || mismatch then some ⟨query.names, [], none⟩
    else none
  | .insertSelect _ _ _ _ returning _ subqueries _ =>
    let context := Resolved.statementContext clock counters parameters before.database subqueries
    let written := run.keyRows.getD []
    if successful then
      some ⟨returning.map (·.2), returnedRows context returning (written.map (·.values)), some (run.counts.changes.getD 0)⟩
    else if constraintFailure || overflow || functionFailure then
      some ⟨returning.map (·.2), [], some (run.counts.changes.getD 0)⟩
    else none
  | .insert _ _ returning subqueries (some _) | .upsert _ _ _ returning _ subqueries (some _)
  | .update _ _ _ returning subqueries (some _) | .delete _ _ returning subqueries (some _) =>
    let context := Resolved.statementContext clock counters parameters before.database subqueries
    let written := run.keyRows.getD []
    if successful then
      some ⟨returning.map (·.2), returnedRows context returning (written.map (·.values)), some (run.counts.changes.getD 0)⟩
    else if constraintFailure then some ⟨returning.map (·.2), [], some (run.counts.changes.getD 0)⟩ else none
  | .addColumn _ column refuses => some ⟨addColumnOutputNames column refuses, [], none⟩
  | .createTable .. | .createView .. | .createIndex .. | .createTrigger .. | .rewrite _ | .dropColumn .. | .drop .. | .begin | .commit | .rollback | .prepareError _
  | .setting .. => some ⟨[], [], none⟩

end Belay.Sqlite.Model
