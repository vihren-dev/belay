import Belay.Sqlite.Programs.Reasoning.ExecutionDeterministic
import Belay.Sqlite.Queries.Evaluation.NotInQuery

set_option doc.verso true

/-! The equivalence of {lit}`x NOT IN (SELECT c FROM u)` and the correlated {lit}`NOT EXISTS (SELECT 1 FROM u WHERE
u.c = x)` as {lit}`Sql.EquivAt` (ADR 0017, S4 and S6), and of {lit}`x IN (SELECT c FROM u)` and the correlated
{lit}`EXISTS`. The lemmas are general over the tables, the columns, the names and the syntax of the two statements:
they take the continuing frame and the modeled output of each actual statement. For a SELECT, its frame and the resolution laws can supply this evidence
({lit}`resolveStatement_selectFrom_inQuery` and {lit}`resolveStatement_selectFrom_existsTest`). The structural premises describe the tables of the connection. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- For every two scripts of one statement each and every context: if the step of the first statement gives the
rows {lit}`rows`, keeps the connection and has no further execution, and the step of the second statement gives the
same rows, keeps the connection and has no further execution, the two scripts are equivalent at the context ({name}`Sql.EquivAt`). Plain words: two single queries that
read the same rows and change nothing are equivalent, with the same actual run and the same branches. Proof sketch:
an output of rows is not a choice, so each program has one branch ({name}`Sql.EquivAt.of_one_branch`), and the two
actual runs are equal by the two steps. -/
theorem Sql.EquivAt.of_select_steps {first second : Script} {state : ExecutionContext}
    {firstStatement secondStatement : Syntax.Statement} {firstValues secondValues : List Value}
    {rows : List (List Value)}
    (firstStatements : first.statements = [(firstStatement, firstValues)])
    (secondStatements : second.statements = [(secondStatement, secondValues)])
    (leftStep : runScriptStep runContext state.clock state.index state.connection firstStatement firstValues =
      .continued (.rows rows) state.connection [])
    (rightStep : runScriptStep runContext state.clock state.index state.connection secondStatement secondValues =
      .continued (.rows rows) state.connection []) :
    Sql.EquivAt (send first) (send second) state := by
  unfold send
  rw [firstStatements, secondStatements]
  refine Sql.EquivAt.of_one_branch
    (by simp [Sql.hasOneBranch, sendStatements, Sql.map, leftStep, Model.Output.choosesResults])
    (by simp [Sql.hasOneBranch, sendStatements, Sql.map, rightStep, Model.Output.choosesResults]) ?_
  simp [Sql.runFrom, sendStatements, Sql.map, leftStep, rightStep]

/-- For every execution context, two single-statement scripts with the same bound values,
two table positions, result names, projection columns and collations, assume all of the following.

* Each continuing execution of the first statement keeps the connection and has no further executions.
* Each continuing execution of the second statement keeps the connection and has no further executions.
* At this context and these parameter values the first step has the output of the outer scan projecting
  {lit}`columns` with condition {lit}`key NOT IN` subquery 0. That subquery selects {lit}`column`
  from the inner table with no filter.
* At the same inputs the second step has the output of the same projection with condition
  {lit}`NOT EXISTS` subquery 0. That subquery selects 1 from the inner table where its column
  (at offset {lit}`outer + column`) equals the outer key with the same affinity.
* {lit}`keyInside`: the key position is below the outer width. {lit}`presentOuter` and
  {lit}`presentInner`: the connection has the two indicated tables at their respective positions.
* {lit}`alias`: the outer key is its rowid alias. {lit}`aliased`: its value in every outer
  row equals that row's rowid. {lit}`notText`: comparison affinity is not TEXT.
* {lit}`known`: the inner column is non-NULL in every source row.

Then sending the two scripts gives equal actual runs and branch sets at this context
({name}`Sql.EquivAt`). Without the non-NULL premise a NULL can change NOT IN.
Proof sketch: {name}`resolvedStepOutput_notIn_eq_notExists_of_rowidAlias` identifies both row
outputs. The two frames and {name}`RunStep.eq_of_rows` give the two full steps
for {name}`Sql.EquivAt.of_select_steps`. -/
theorem Sql.EquivAt.notIn_notExists_of_rowidAlias {first second : Script} {state : ExecutionContext}
    {parameters : List Value}
    {firstStatement secondStatement : Syntax.Statement}
    (firstFrame : ∀ output next others, runScriptStep runContext state.clock state.index state.connection
      firstStatement parameters = .continued output next others → others = [] ∧ next = state.connection)
    (secondFrame : ∀ output next others, runScriptStep runContext state.clock state.index state.connection
      secondStatement parameters = .continued output next others → others = [] ∧ next = state.connection)
    (outerPosition innerPosition outer column key : Nat) (outerTable innerTable : Table) (columns : List Nat)
    (namesMain namesIn namesExists : List String) (affinity : Option Affinity) (inCollation equalsCollation : Collation)
    (keyInside : key < outer)
    (presentOuter : state.connection.state.database.table outerPosition = some outerTable)
    (presentInner : state.connection.state.database.table innerPosition = some innerTable)
    (alias : outerTable.shape.rowidAlias = some key) (aliased : outerTable.RowsAliased)
    (notText : affinity ≠ some .text)
    (known : ∀ cells ∈ Resolved.sourceRows innerTable, (cells.getD column .null).isNull = false)
    (firstStatements : first.statements = [(firstStatement, parameters)])
    (secondStatements : second.statements = [(secondStatement, parameters)])
    (firstOutput : (runScriptStep runContext state.clock state.index state.connection firstStatement parameters).output =
      resolvedStepOutput state.clock state.index state.connection parameters (.query (Resolved.Query.oneTable outerPosition 0
          (some (.inQuery (.column key) 0 affinity inCollation true)) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer none [.column (outer + column)] namesIn]))
    (secondOutput : (runScriptStep runContext state.clock state.index state.connection secondStatement parameters).output =
      resolvedStepOutput state.clock state.index state.connection parameters (.query (Resolved.Query.oneTable outerPosition 0 (some (.not (.exists 0))) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer
          (some (.compare .eq affinity (.column (outer + column)) (.column key) equalsCollation))
          [.literal (.integer 1)] namesExists])) :
    Sql.EquivAt (send first) (send second) state := by
  obtain ⟨rows, leftRows, rightRows⟩ := resolvedStepOutput_notIn_eq_notExists_of_rowidAlias state.clock state.index
    outerPosition innerPosition outer column key state.connection parameters outerTable innerTable columns namesMain
    namesIn namesExists affinity inCollation equalsCollation keyInside presentOuter presentInner alias aliased notText known
  exact Sql.EquivAt.of_select_steps firstStatements secondStatements
    (RunStep.eq_of_rows firstFrame (by rw [firstOutput]; exact leftRows))
    (RunStep.eq_of_rows secondFrame (by rw [secondOutput]; exact rightRows))

/-- **IN against EXISTS, as execution equivalence.** For the same context, tables, columns and key as in
{name}`Sql.EquivAt.notIn_notExists_of_rowidAlias`, assume both continuing steps preserve the connection
and have no further executions. With the output of {lit}`x IN` subquery 0 for the first statement and
the output of {lit}`EXISTS` subquery 0 for the second, the two scripts are equivalent at the context under the premises
{lit}`keyInside`, {lit}`presentOuter`, {lit}`presentInner`, {lit}`alias`, {lit}`aliased` and {lit}`notText`. It needs no premise on NULL cells of the column, and the collations are
free. Proof sketch: as for {name}`Sql.EquivAt.notIn_notExists_of_rowidAlias`, with
{name}`resolvedStepOutput_in_eq_exists_of_rowidAlias`. -/
theorem Sql.EquivAt.in_exists_of_rowidAlias {first second : Script} {state : ExecutionContext}
    {parameters : List Value}
    {firstStatement secondStatement : Syntax.Statement}
    (firstFrame : ∀ output next others, runScriptStep runContext state.clock state.index state.connection
      firstStatement parameters = .continued output next others → others = [] ∧ next = state.connection)
    (secondFrame : ∀ output next others, runScriptStep runContext state.clock state.index state.connection
      secondStatement parameters = .continued output next others → others = [] ∧ next = state.connection)
    (outerPosition innerPosition outer column key : Nat) (outerTable innerTable : Table) (columns : List Nat)
    (namesMain namesIn namesExists : List String) (affinity : Option Affinity) (inCollation equalsCollation : Collation)
    (keyInside : key < outer)
    (presentOuter : state.connection.state.database.table outerPosition = some outerTable)
    (presentInner : state.connection.state.database.table innerPosition = some innerTable)
    (alias : outerTable.shape.rowidAlias = some key) (aliased : outerTable.RowsAliased)
    (notText : affinity ≠ some .text)
    (firstStatements : first.statements = [(firstStatement, parameters)])
    (secondStatements : second.statements = [(secondStatement, parameters)])
    (firstOutput : (runScriptStep runContext state.clock state.index state.connection firstStatement parameters).output =
      resolvedStepOutput state.clock state.index state.connection parameters (.query (Resolved.Query.oneTable outerPosition 0
          (some (.inQuery (.column key) 0 affinity inCollation false)) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer none [.column (outer + column)] namesIn]))
    (secondOutput : (runScriptStep runContext state.clock state.index state.connection secondStatement parameters).output =
      resolvedStepOutput state.clock state.index state.connection parameters (.query (Resolved.Query.oneTable outerPosition 0 (some (.exists 0)) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer
          (some (.compare .eq affinity (.column (outer + column)) (.column key) equalsCollation))
          [.literal (.integer 1)] namesExists])) :
    Sql.EquivAt (send first) (send second) state := by
  obtain ⟨rows, leftRows, rightRows⟩ := resolvedStepOutput_in_eq_exists_of_rowidAlias state.clock state.index
    outerPosition innerPosition outer column key state.connection parameters outerTable innerTable columns namesMain
    namesIn namesExists affinity inCollation equalsCollation keyInside presentOuter presentInner alias aliased notText
  exact Sql.EquivAt.of_select_steps firstStatements secondStatements
    (RunStep.eq_of_rows firstFrame (by rw [firstOutput]; exact leftRows))
    (RunStep.eq_of_rows secondFrame (by rw [secondOutput]; exact rightRows))

end Belay.Sqlite
