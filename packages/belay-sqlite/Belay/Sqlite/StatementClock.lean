import Belay.Sqlite.Resolution.Resolved
import Belay.Sqlite.Resolution.StatementCatalog
import Belay.Sqlite.ClockReads
import Belay.Sqlite.StoreValue
import Belay.Sqlite.QueryEval

set_option doc.verso true

/-! The clock of a resolved statement (ADR 0012, amendment 5, slice 6e2; ADR 0013, D6): the
cells of a {lit}`Statement.clocked` INSERT at the statement's clock value, and whether a
statement reads the clock at all. Evaluation takes the clock value as a parameter, so a
statement is never rewritten for a clock value. -/

namespace Belay.Sqlite.Resolved

/-- The rows of an INSERT with one cell set to its value at a clock value: the value of
the cell's expression, which reads no column, stored with the cell's affinity. -/
def ClockCell.fill (clock : Int) (rows : List (List Value)) (cell : ClockCell) : List (List Value) :=
  rows.modify cell.row fun row => row.set cell.column (storeValue cell.affinity (cell.value.eval clock []))

/-- An INSERT with its cells set to their values at a clock value ({name}`ClockCell.fill`);
any other statement unchanged. -/
def Statement.fillCells (clock : Int) (cells : List ClockCell) : Statement → Statement
  | .insert target rows returning => .insert target (cells.foldl (ClockCell.fill clock) rows) returning
  | .upsert target rows clauses returning algorithm =>
    .upsert target (cells.foldl (ClockCell.fill clock) rows) clauses returning algorithm
  | statement@(.update ..) | statement@(.delete ..) | statement@(.query _) | statement@(.clocked ..)
  | statement@(.createTable ..) | statement@(.createIndex ..) | statement@(.addColumn ..) | statement@.begin
  | statement@.commit | statement@.rollback | statement@(.prepareError _) => statement

/-- A statement ready to run at a clock value: a clocked INSERT with its cells filled in
({name}`Statement.fillCells`); any other statement unchanged. -/
def Statement.unclock (clock : Int) : Statement → Statement
  | .clocked statement cells => statement.fillCells clock cells
  | statement@(.insert ..) | statement@(.upsert ..) | statement@(.update ..) | statement@(.delete ..)
  | statement@(.query _) | statement@(.createTable ..) | statement@(.createIndex ..) | statement@(.addColumn ..)
  | statement@.begin | statement@.commit | statement@.rollback | statement@(.prepareError _) => statement

/-- For every clock value and statement, the statement ready to run
({name}`Statement.unclock`) has the catalog effect ({name}`Statement.applyCatalog`) and the
transaction-control flag ({name}`Statement.isControl`) of the statement. Proof sketch: only a
clocked INSERT changes, into its INSERT with filled cells, which has the effect and flag
that the clocked INSERT takes from it. -/
theorem Statement.unclock_catalog (clock : Int) (statement : Statement) :
    (statement.unclock clock).applyCatalog = statement.applyCatalog ∧
      (statement.unclock clock).isControl = statement.isControl := by
  cases statement with
  | clocked inner cells =>
    cases inner <;> exact ⟨rfl, rfl⟩
  | _ => exact ⟨rfl, rfl⟩

/-- The expressions of an aggregate result column: its operand, none for {lit}`COUNT(*)`. -/
def Aggregate.expressions : Aggregate → List Expr
  | .countRows => []
  | .count operand | .min operand | .max operand | .sum operand | .avg operand => [operand]

/-- The expressions of a result column. -/
def Output.expressions : Output → List Expr
  | .scalar term => [term]
  | .aggregate function => function.expressions

/-- Every expression of a query: the arguments and {lit}`ON` condition of each source,
{lit}`WHERE`, {lit}`GROUP BY`, the result columns and the {lit}`ORDER BY` expressions. -/
def Query.clockExpressions (query : Query) : List Expr :=
  query.sources.flatMap (fun join => (match join.source with
    | .each json path => json :: path.toList
    | .table _ | .subquery => []) ++ join.condition.toList) ++
  query.filter.toList ++ query.groupBy ++ query.columns.flatMap Output.expressions ++
  query.orderBy.flatMap fun (key, _) => match key with
    | .expression term => [term]
    | .output _ => []

/-- The expressions of an {lit}`ON CONFLICT` clause: the values and the filter of
{lit}`DO UPDATE`. -/
def ConflictClause.clockExpressions (clause : ConflictClause) : List Expr :=
  match clause.action with
  | .nothing => []
  | .update assignments filter => assignments.map (·.2) ++ filter.toList

/-- Every expression of a statement that evaluation reads: the {lit}`RETURNING` columns,
the values and filters of writes, the clauses of an upsert and the expressions of a query
({name}`Query.clockExpressions`). A clocked INSERT gives the expressions of its cells and
of its statement; a schema or transaction statement and a prepare error have none. -/
def Statement.clockExpressions : Statement → List Expr
  | .insert _ _ returning => returning.map (·.1)
  | .upsert _ _ clauses returning _ => clauses.flatMap ConflictClause.clockExpressions ++ returning.map (·.1)
  | .update _ assignments filter returning => assignments.map (·.2) ++ filter.toList ++ returning.map (·.1)
  | .delete _ filter returning => filter.toList ++ returning.map (·.1)
  | .query inner => inner.clockExpressions
  | .clocked statement cells => cells.map (·.value) ++ statement.clockExpressions
  | .createTable .. | .createIndex .. | .addColumn .. | .begin | .commit | .rollback | .prepareError _ => []

/-- Whether a statement reads the clock: a clocked INSERT, or a statement with an
expression that reads it ({name}`Expr.readsClock`). The execution gives a statement that
does not the clock value 0, which it does not read ({lit}`runSqlAt`). -/
def Statement.readsClock : Statement → Bool
  | .clocked .. => true
  | statement@(.insert ..) | statement@(.upsert ..) | statement@(.update ..) | statement@(.delete ..)
  | statement@(.query _) | statement@(.createTable ..) | statement@(.createIndex ..) | statement@(.addColumn ..)
  | statement@.begin | statement@.commit | statement@.rollback | statement@(.prepareError _) =>
    statement.clockExpressions.any Expr.readsClock

end Belay.Sqlite.Resolved
