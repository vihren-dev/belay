import Belay.Sqlite.Model.InsertSelectSource
import Belay.Sqlite.Model.UpsertRun
import Belay.Sqlite.Model.PlainCounts
import Belay.Sqlite.Model.StatementRun
import Belay.Sqlite.Model.StatementClock
import Belay.Sqlite.Model.JsonReady

set_option doc.verso true

/-! The run of INSERT from a query (ADR 0019, D4, amended 2026-10-25). The query gives a production
({lit}`SourceProduction`): the rows that it hands to the INSERT and the failure that
ends them. The INSERT writes the rows as INSERT with {lit}`VALUES` does ({lit}`LiteralData.upsertSteps`),
one at a time, so an earlier conflict stops the statement before a later source failure, and a source
failure after rows that all succeed stops it after their writes, which a statement error rolls back:
it keeps no row (checked natively with 3.51.0, also with {lit}`OR FAIL`), counts none as changed, and
leaves {lit}`last_insert_rowid()` at the last row inserted. Each order in which SQLite may read the
query is one admitted execution; the first is the model's own run. -/

namespace Belay.Sqlite.Model

/-- The value of a cell of INSERT from a query for the column of the affinity, over one row of the
query: a result column of the row stored with the affinity ({name}`Value.store`), or a cell that does
not read the query ({name}`Resolved.Cell.valueAt`). -/
def Resolved.SourceCell.valueOver (context : Resolved.EvalContext) (affinity : Affinity) (row : List Value) :
    Resolved.SourceCell → Value
  | .source column => Value.store affinity (row.getD column .null)
  | .cell fixed => fixed.valueAt context affinity

/-- The full rows that an INSERT from a query writes for the rows of a production, in table order
({name}`Resolved.SourceCell.valueOver`). -/
def insertSelectRows (context : Resolved.EvalContext) (columns : List CatalogColumn) (cells : List Resolved.SourceCell)
    (rows : List (List Value)) : List (List Value) :=
  rows.map fun row => cells.zipIdx.map fun (cell, index) =>
    cell.valueOver context ((columns[index]?.map CatalogColumn.affinity).getD .blob) row

/-- Whether SQLite collects the rows of the query before it writes the first one: the query or a
subquery reads the written table, a trigger of INSERT on the table exists, or the INSERT has
{lit}`RETURNING`, which SQLite runs as a trigger. -/
def Resolved.Statement.collectsSource (target : Nat) (query : Resolved.Query) (subqueries : List Resolved.Query)
    (returning : List (Resolved.Expr × String)) (rules : Option Resolved.WriteRules) : Bool :=
  query.readsTable target || subqueries.any (·.readsTable target) || !returning.isEmpty ||
    rules.any fun rules => rules.programs.any fun program => program.table == target && program.event == .insert

/-- The run of INSERT from a query for one production ({name}`SourceProduction`) over the table: the
rows are written as {name}`Resolved.Statement.upsert` writes its rows, and a failure of the production
after rows that all succeed ends the statement with that error and the input database. -/
def insertSelectOutcome (clock : Int) (context : Resolved.EvalContext) (database : Database) (target : Nat) (table : Table)
    (cells : List Resolved.SourceCell) (clauses : List Resolved.ConflictClause) (algorithm : Option ConflictAlgorithm)
    (rules : Option Resolved.WriteRules) (plain : Bool) (production : SourceProduction) : StatementRun :=
  let keys := database.keys target table
  let policy := database.catalog.writePolicy target table.shape algorithm
  let values := insertSelectRows context table.shape.columns cells production.rows
  let steps := LiteralData.upsertSteps context keys policy clauses table values
  let summary := LiteralData.upsertSummary table steps
  let sourceFailure := production.failure.map SourceFailure.toError
  let failure := match summary with
    | .ok _ => sourceFailure
    | .error (reason, _, _) => some reason
  let effect : Effect := match summary with
    | .ok (result, _) => match sourceFailure with
      | none => .ok (database.setRows target result.rows)
      | some reason => .error (reason, database)
    | .error (reason, reached, _) => .error (reason, database.setRows target reached.rows)
  let run := StatementRun.withKeys effect
    (LiteralData.upsertReady keys table clauses values steps)
    (LiteralData.upsertCounts keys clauses table.shape steps failure)
    (rules.map fun rules => insertKeys rules clock target policy clauses values database plain algorithm true sourceFailure)
  { run with keyRows := run.keyRows <|> some (LiteralData.upsertWritten steps) }

/-- The rowids of the source rows when SQLite may copy the rows of the query by its transfer
optimization ({lit}`xferOptimization` of {lit}`sqlite3Insert`), else none. The optimization applies to
a statement of the form {lit}`INSERT INTO t SELECT * FROM s`: no column list, no filter, no window, no
grouping, one other table as the source, and no trigger or key rule. When the written table has an
index and no rowid alias, SQLite then writes each row under the rowid that it has in the source,
which the model does not describe ({lit}`insertSelectTransferReady`). The model takes every query of
this form that fills each column in order from the columns of the source in order, also one that lists
those columns, as a candidate; a query with another result column, such as {lit}`abs(x)`, is not one. -/
def insertSelectTransferRowids (target : Nat) (cells : List Resolved.SourceCell) (query : Resolved.Query) (table : Table)
    (database : Database) (rules : Option Resolved.WriteRules) : Option (List Int) :=
  match query.sources with
  | [{ source := .table position, .. }] =>
    if position != target && rules.isNone && !table.shape.withoutRowid && table.shape.rowidAlias.isNone &&
        !(database.catalog.accessKeys target table.shape).isEmpty && query.filter.isNone && !query.aggregate &&
        query.compound.isNone && query.distinct.isNone && query.orderBy.isEmpty && query.limit.isNone &&
        query.limitParameter.isNone && query.offset == 0 && query.offsetParameter.isNone &&
        cells == (List.range table.shape.columns.length).map Resolved.SourceCell.source &&
        query.columns == (List.range table.shape.columns.length).map fun position => .scalar (.column position) then
      (database.table position).map fun source => source.scanRows.map (·.rowid)
    else none
  | _ => none

/-- Whether the run of the first production agrees with SQLite's transfer optimization: a statement
that the optimization may copy ({name}`insertSelectTransferRowids`) writes its rows under the rowids
that the model assigns one after the other. When a run does not, the model has no description of the
statement, and its run is not ready. -/
def insertSelectTransferReady (rowids : Option (List Int)) (main : StatementRun) : Bool :=
  match rowids, main.effect with
  | none, _ => true
  | some _, .error _ => false
  | some source, .ok _ => (main.keyRows.getD []).map (·.rowid) == source

/-- The run of INSERT from a query on a database (ADR 0019, D4): the run of its first production
as the statement's own run, and, for a statement without rules, the run of each other production as
an alternative execution, each with its own effect, counts and written rows. The run is ready when
every execution is, no further execution is an error with the reason {name}`ExecutionError.unmodeled`
({name}`Effect.isModeled`: such an execution has no output and would end the run), the query is plain
(also the terms of a compound: the laws of the statement read the query as an upsert), and the statement has no cell, clause or {lit}`RETURNING` expression that can
fail. A statement for which the model has no production is not ready, and neither is one that SQLite
may copy under rowids that the model does not assign ({name}`insertSelectTransferReady`). A statement
with rules (a trigger or an enforced foreign key) is described for one production only: with more
than one it is not ready, and its run has no alternative. -/
def insertSelectRun (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat)
    (cells : List Resolved.SourceCell) (query : Resolved.Query) (clauses : List Resolved.ConflictClause)
    (returning : List (Resolved.Expr × String)) (algorithm : Option ConflictAlgorithm)
    (subqueries : List Resolved.Query) (rules : Option Resolved.WriteRules) (database : Database) : StatementRun :=
  match database.table target with
  | none => { effect := .error (.unmodeled, database), ready := true }
  | some table =>
    let context := Resolved.statementContext clock counters parameters database subqueries
    let collects := Resolved.Statement.collectsSource target query subqueries returning rules
    match query.productions context database !collects with
    | none | some [] => { effect := .error (.unmodeled, database), ready := false }
    | some (first :: others) =>
      let run := insertSelectOutcome clock context database target table cells clauses algorithm rules subqueries.isEmpty
      let main := run first
      let rest := others.map run
      { main with
        ready := main.ready && rest.all (fun other => other.ready && other.effect.isModeled) && (rules.isNone || others.isEmpty) &&
          insertSelectTransferReady (insertSelectTransferRowids target cells query table database rules) main && Resolved.subqueriesPlain subqueries &&
          Resolved.cellsReady context [cells.filterMap fun | .cell fixed => some fixed | .source _ => none] &&
          upsertJsonReady clauses returning,
        alternatives := if rules.isNone then rest.map fun other => { effect := other.effect, counts := other.counts, keyRows := other.keyRows }
          else [] }

end Belay.Sqlite.Model
