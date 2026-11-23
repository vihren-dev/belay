import Belay.Sqlite.Model.Programs.Scripts.PlainInsertRule
import Belay.Sqlite.Model.Programs.Scripts.StepCase

set_option doc.verso true

/-! The case type of plain INSERT (statement rule pilot, "Case type of plain INSERT"): an INSERT of rows without a
RETURNING clause and without write rules. {lit}`PlainInsertCase` gives the cases of the run of the statement at a
clock value, and {lit}`StepCase` with it gives all cases of the step. Cover says that the step is in a case, one
result says that the cases give one result, and {lit}`runScriptStep_plainInsert_of_case` gives the step equation
of each case. A forward proof builds one case and uses its equation. A proof about each input splits the cover
with {lit}`cases` or {lit}`rcases`. -/

namespace Belay.Sqlite.Model

/-- The cases of the run of a plain INSERT at a clock value, after the checks of the clock and the counters, for the
connection, the parameter values, the target position, the rows of cells and the subqueries. The values of the rows
are the cells evaluated in the context of the clock value, the counters, the parameter values, the database and the
subqueries ({name}`Resolved.rowsAt`). A result is in a case when one of these holds:
* {lit}`noTable`: the target holds no table, and the run ends with {name}`unmodeledHere`;
* {lit}`unready`: the target holds the table, and the readiness check of the table and the values
  ({name}`LiteralData.insertReady`), the subquery check ({name}`Resolved.subqueriesPlain`) or the cell check
  ({name}`Resolved.cellsReady`) fails, and the run ends with {name}`unmodeledHere`;
* {lit}`success`: the target holds the table, the three checks pass, and the outcome ({name}`insertOutcome`) is the
  database {lit}`written`; the step continues with {lit}`.done rows.length`, the connection after the write
  ({name}`Connection.afterWrite`) of that database with the counts of the insertion, and no further execution;
* {lit}`failure`: the target holds the table, the three checks pass, and the outcome is an error with the reason
  and the database before; the step continues with the error output of the primary code of the reason, the
  connection after the write of the database before with the counts of the failed insertion, and no further
  execution.
The table and the values are arguments of the cases, so a proof does not restate how they are computed. -/
inductive PlainInsertCase (connection : Connection) (parameters : List Value) (target : Nat)
    (rows : List (List Resolved.Cell)) (subqueries : List Resolved.Query) (value : Int) : RunStep → Prop where
  /-- The target holds no table, so the run ends. -/
  | noTable (located : connection.state.database.table target = none) :
      PlainInsertCase connection parameters target rows subqueries value (.ended unmodeledHere)
  /-- The target holds the table, and a check of the statement fails, so the run ends. -/
  | unready {table : Table} {values : List (List Value)} (located : connection.state.database.table target = some table)
      (evaluated : Resolved.rowsAt (Resolved.statementContext value (connection.state.counters.view
        (Resolved.Statement.insert target rows [] subqueries none).counterReads) parameters connection.state.database
        subqueries) table.shape.columns rows = values)
      (failed : (LiteralData.insertReady (connection.state.database.keys target table) table values
        (LiteralData.inserted table values) && Resolved.subqueriesPlain subqueries &&
        Resolved.cellsReady (Resolved.statementContext value (connection.state.counters.view
          (Resolved.Statement.insert target rows [] subqueries none).counterReads) parameters connection.state.database
          subqueries) rows) = false) :
      PlainInsertCase connection parameters target rows subqueries value (.ended unmodeledHere)
  /-- The checks pass and the outcome is the database {lit}`written`: the step continues with the number of rows and
  the connection after the write of that database. -/
  | success {table : Table} {values : List (List Value)} {written : Database}
      (located : connection.state.database.table target = some table)
      (evaluated : Resolved.rowsAt (Resolved.statementContext value (connection.state.counters.view
        (Resolved.Statement.insert target rows [] subqueries none).counterReads) parameters connection.state.database
        subqueries) table.shape.columns rows = values)
      (ready : LiteralData.insertReady (connection.state.database.keys target table) table values
        (LiteralData.inserted table values) = true)
      (plain : Resolved.subqueriesPlain subqueries = true)
      (cells : Resolved.cellsReady (Resolved.statementContext value (connection.state.counters.view
        (Resolved.Statement.insert target rows [] subqueries none).counterReads) parameters connection.state.database
        subqueries) rows = true)
      (outcome : insertOutcome connection.state.database target (connection.state.database.keys target table) table
        values (LiteralData.inserted table values) = .ok written) :
      PlainInsertCase connection parameters target rows subqueries value (.continued (.done rows.length)
        (connection.afterWrite written
          (LiteralData.insertCounts (.ok written) (connection.state.database.keys target table) table values)) [])
  /-- The checks pass and the insertion fails: the step continues with the error code. -/
  | failure {table : Table} {values : List (List Value)} {reason : ExecutionError}
      (located : connection.state.database.table target = some table)
      (evaluated : Resolved.rowsAt (Resolved.statementContext value (connection.state.counters.view
        (Resolved.Statement.insert target rows [] subqueries none).counterReads) parameters connection.state.database
        subqueries) table.shape.columns rows = values)
      (ready : LiteralData.insertReady (connection.state.database.keys target table) table values
        (LiteralData.inserted table values) = true)
      (plain : Resolved.subqueriesPlain subqueries = true)
      (cells : Resolved.cellsReady (Resolved.statementContext value (connection.state.counters.view
        (Resolved.Statement.insert target rows [] subqueries none).counterReads) parameters connection.state.database
        subqueries) rows = true)
      (outcome : insertOutcome connection.state.database target (connection.state.database.keys target table) table
        values (LiteralData.inserted table values) = .error (reason, connection.state.database)) :
      PlainInsertCase connection parameters target rows subqueries value (.continued (.error reason.primaryCode)
        (connection.afterWrite connection.state.database (LiteralData.insertCounts
          (.error (reason, connection.state.database)) (connection.state.database.keys target table) table values)) [])

/-- For every connection, parameter values, target, rows of cells, subqueries and clock value: two results that
{name}`PlainInsertCase` relates to these inputs are equal. In plain words, the cases of plain INSERT give one result.
Proof sketch: the table, the values, the checks and the outcome are functions of the inputs, so two cases agree on
them; the premises of two different cases contradict. -/
theorem PlainInsertCase.unique {connection : Connection} {parameters : List Value} {target : Nat}
    {rows : List (List Resolved.Cell)} {subqueries : List Resolved.Query} {value : Int} {first second : RunStep}
    (one : PlainInsertCase connection parameters target rows subqueries value first)
    (two : PlainInsertCase connection parameters target rows subqueries value second) : first = second := by
  cases one <;> cases two <;> simp_all

/-- The cover of plain INSERT. For every resolution context, clock, index, connection, statement, parameter values,
resolution state, target, rows of cells and subqueries: if the statement resolves to an INSERT of the rows into the
target with the subqueries, without a RETURNING clause and without write rules, then {name}`StepCase` with
{name}`PlainInsertCase` relates the inputs to the step of the statement. In plain words, the step of each plain
INSERT is in a case. Proof sketch: rewrite the step with {name}`runScriptStep_plainInsert_eq`;
{name}`StepCase.of_checks` gives the checks of the clock and the counters; split on the table, the checks and the
outcome, and {name}`insertOutcome_error` gives the database of an error. -/
theorem runScriptStep_plainInsert_cover {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {rows : List (List Resolved.Cell)} {subqueries : List Resolved.Query}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insert target rows [] subqueries none, after)) :
    StepCase clock index connection (.insert target rows [] subqueries none)
      (PlainInsertCase connection parameters target rows subqueries)
      (runScriptStep context clock index connection statement parameters) := by
  rw [runScriptStep_plainInsert_eq found]
  refine StepCase.of_checks fun value _ _ => ?_
  dsimp only
  cases located : connection.state.database.table target with
  | none => exact .noTable located
  | some table =>
    dsimp only
    split
    · rename_i checks
      simp only [Bool.and_eq_true] at checks
      obtain ⟨⟨ready, plain⟩, cells⟩ := checks
      split
      · rename_i written outcome
        rw [outcome, ← insertOutcome_ok outcome]
        exact .success located rfl ready plain cells outcome
      · rename_i reason reached outcome
        obtain ⟨rfl, -⟩ := insertOutcome_error outcome
        rw [outcome]
        exact .failure located rfl ready plain cells outcome
    · rename_i failed
      exact .unready located rfl (Bool.eq_false_iff.mpr failed)

/-- The step equation of plain INSERT. For every resolution context, clock, index, connection, statement, parameter
values, resolution state, target, rows of cells, subqueries and result: if the statement resolves to an INSERT of
the rows into the target with the subqueries, without a RETURNING clause and without write rules, and
{name}`StepCase` with {name}`PlainInsertCase` relates the inputs to the result, then the step of the statement is
that result. In plain words, each case gives the equation of the step. Proof: {name}`RunStep.eq_of_cover` with
{name}`runScriptStep_plainInsert_cover`, {name}`StepCase.unique` and {name}`PlainInsertCase.unique`. -/
theorem runScriptStep_plainInsert_of_case {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {rows : List (List Resolved.Cell)} {subqueries : List Resolved.Query} {result : RunStep}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insert target rows [] subqueries none, after))
    (case : StepCase clock index connection (.insert target rows [] subqueries none)
      (PlainInsertCase connection parameters target rows subqueries) result) :
    runScriptStep context clock index connection statement parameters = result :=
  RunStep.eq_of_cover (runScriptStep_plainInsert_cover found)
    (fun _ _ => StepCase.unique (kindCase := PlainInsertCase connection parameters target rows subqueries)
      fun _ _ _ => PlainInsertCase.unique) case

end Belay.Sqlite.Model
