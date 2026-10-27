import Belay.Sqlite.ExecutionDeterministic
import Belay.Sqlite.Model

set_option doc.verso true

/-! The equivalence of {lit}`x NOT IN (SELECT c FROM u)` and the correlated {lit}`NOT EXISTS (SELECT 1 FROM u WHERE
u.c = x)` as {lit}`Sql.EquivAt` (ADR 0017, S4 and S6), and of {lit}`x IN (SELECT c FROM u)` and the correlated
{lit}`EXISTS`. The lemmas are general over the tables, the columns, the names and the syntax of the two statements:
they take the resolution of each statement as a hypothesis, in the form that the resolution laws of the model give
({lit}`resolveStatement_selectFrom_inQuery` and {lit}`resolveStatement_selectFrom_existsTest`), and the structural
premises as facts about the tables of the connection. The statements are in {lit}`NotExistsQuery.lean` and
{lit}`ExistsQuery.lean` for the uncorrelated forms. -/

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

/-- Whether a statement is a {lit}`SELECT`, whatever its parts: it is {lit}`.select` of some result columns, source,
joins, filter, grouping, ordering, limit, offset, subqueries, having clause, distinct flag and compound part. Plain
words: the statement is a query statement of the select kind, and nothing else is said about it. -/
def IsSelectStatement (statement : Syntax.Statement) : Prop :=
  ∃ columns source joins filter groupBy orderBy limit offset subqueries having distinct compound,
    statement = .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound

/-- For every statement that is a {lit}`SELECT` and every context: if the output of its step is the rows {lit}`rows`,
the step continues with them, keeps the connection and has no further execution. Plain words: a SELECT that gives
rows changes nothing. Proof sketch: take the parts of the statement and apply {name}`runScriptStep_select_rows`. -/
theorem IsSelectStatement.step_of_rows {statement : Syntax.Statement} (isSelect : IsSelectStatement statement)
    {clock : Option Clock} {index : Nat} {connection : Connection} {values : List Value} {rows : List (List Value)}
    (output : (runScriptStep runContext clock index connection statement values).output = .rows rows) :
    runScriptStep runContext clock index connection statement values = .continued (.rows rows) connection [] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, same⟩ := isSelect
  exact runScriptStep_select_rows same output

/-- **NOT IN against NOT EXISTS, as execution equivalence.** For every context, two scripts of one statement each (both
statements are SELECT statements, {name}`IsSelectStatement`), and two tables of the connection at positions: if the first statement resolves to the query of the outer table whose
condition is {lit}`x NOT IN` subquery 0 on the column {lit}`key`, with the one subquery that selects the column
{lit}`column` of the inner table with no condition, and the second statement resolves to the query of the outer table
whose condition is {lit}`NOT EXISTS` subquery 0, with the one subquery that selects 1 from the inner table where
{lit}`u.c = x` ({lit}`.compare .eq`) with the same affinity, then the two scripts are equivalent at the context
({lit}`Sql.EquivAt`), under these premises:
* both statements have the same values and the same result columns (positions {lit}`columns`) of the outer table;
* the key position is inside the width {lit}`outer` of an outer row ({lit}`keyInside`), and the connection has the outer
  table and the inner table at their positions ({lit}`presentOuter`, {lit}`presentInner`); the subqueries see an outer
  row of the width {lit}`outer`;
* the key column is the rowid alias of the outer table ({lit}`alias`) and every row of the outer table has its alias cell
  equal to its rowid ({lit}`aliased`), so the key cell is a non-NULL integer;
* the comparison affinity is not TEXT ({lit}`notText`);
* no cell of the column in any row of the inner table is NULL ({lit}`known`).
The collations of the two tests are free. Without {lit}`known` the scripts can differ: a NULL cell makes {lit}`NOT IN`
NULL for every row without a match, and {lit}`NOT EXISTS` is true. The statements are any syntax of the select kind that resolves so;
the resolution laws of the model give the hypotheses for the forms of the guide. Proof sketch: the output of each step
is the output of its resolved query ({name}`runScriptStep_output`), the two outputs are the same rows
({name}`resolvedStepOutput_notIn_eq_notExists_of_rowidAlias`), a SELECT step that gives rows keeps the connection
({name}`IsSelectStatement.step_of_rows`), and {name}`Sql.EquivAt.of_select_steps` closes the goal. -/
theorem Sql.EquivAt.notIn_notExists_of_rowidAlias {first second : Script} {state : ExecutionContext}
    {parameters : List Value} {afterFirst afterSecond : ResolveState}
    {firstStatement secondStatement : Syntax.Statement}
    (firstSelect : IsSelectStatement firstStatement) (secondSelect : IsSelectStatement secondStatement)
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
    (firstResolves : resolveStatement runContext state.connection.resolveState
      firstStatement =
      .ok (.query (Resolved.Query.oneTable outerPosition 0
          (some (.inQuery (.column key) 0 affinity inCollation true)) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer none [.column (outer + column)] namesIn], afterFirst))
    (secondResolves : resolveStatement runContext state.connection.resolveState
      secondStatement =
      .ok (.query (Resolved.Query.oneTable outerPosition 0 (some (.not (.exists 0))) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer
          (some (.compare .eq affinity (.column (outer + column)) (.column key) equalsCollation))
          [.literal (.integer 1)] namesExists], afterSecond)) :
    Sql.EquivAt (send first) (send second) state := by
  obtain ⟨rows, leftRows, rightRows⟩ := resolvedStepOutput_notIn_eq_notExists_of_rowidAlias state.clock state.index
    outerPosition innerPosition outer column key state.connection parameters outerTable innerTable columns namesMain
    namesIn namesExists affinity inCollation equalsCollation keyInside presentOuter presentInner alias aliased notText known
  exact Sql.EquivAt.of_select_steps firstStatements secondStatements
    (firstSelect.step_of_rows (by rw [runScriptStep_output, firstResolves]; exact leftRows))
    (secondSelect.step_of_rows (by rw [runScriptStep_output, secondResolves]; exact rightRows))

/-- **IN against EXISTS, as execution equivalence.** For the same context, tables, columns and key as in
{name}`Sql.EquivAt.notIn_notExists_of_rowidAlias`, with SELECT statements, but with {lit}`x IN` subquery 0 for the first statement and
{lit}`EXISTS` subquery 0 for the second, the two scripts are equivalent at the context under the premises
{lit}`keyInside`, {lit}`presentOuter`, {lit}`presentInner`, {lit}`alias`, {lit}`aliased` and {lit}`notText`. It needs no premise on NULL cells of the column, and the collations are
free. Proof sketch: as for {name}`Sql.EquivAt.notIn_notExists_of_rowidAlias`, with
{name}`resolvedStepOutput_in_eq_exists_of_rowidAlias`. -/
theorem Sql.EquivAt.in_exists_of_rowidAlias {first second : Script} {state : ExecutionContext}
    {parameters : List Value} {afterFirst afterSecond : ResolveState}
    {firstStatement secondStatement : Syntax.Statement}
    (firstSelect : IsSelectStatement firstStatement) (secondSelect : IsSelectStatement secondStatement)
    (outerPosition innerPosition outer column key : Nat) (outerTable innerTable : Table) (columns : List Nat)
    (namesMain namesIn namesExists : List String) (affinity : Option Affinity) (inCollation equalsCollation : Collation)
    (keyInside : key < outer)
    (presentOuter : state.connection.state.database.table outerPosition = some outerTable)
    (presentInner : state.connection.state.database.table innerPosition = some innerTable)
    (alias : outerTable.shape.rowidAlias = some key) (aliased : outerTable.RowsAliased)
    (notText : affinity ≠ some .text)
    (firstStatements : first.statements = [(firstStatement, parameters)])
    (secondStatements : second.statements = [(secondStatement, parameters)])
    (firstResolves : resolveStatement runContext state.connection.resolveState
      firstStatement =
      .ok (.query (Resolved.Query.oneTable outerPosition 0
          (some (.inQuery (.column key) 0 affinity inCollation false)) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer none [.column (outer + column)] namesIn], afterFirst))
    (secondResolves : resolveStatement runContext state.connection.resolveState
      secondStatement =
      .ok (.query (Resolved.Query.oneTable outerPosition 0 (some (.exists 0)) (columns.map .column) namesMain)
        [Resolved.Query.oneTable innerPosition outer
          (some (.compare .eq affinity (.column (outer + column)) (.column key) equalsCollation))
          [.literal (.integer 1)] namesExists], afterSecond)) :
    Sql.EquivAt (send first) (send second) state := by
  obtain ⟨rows, leftRows, rightRows⟩ := resolvedStepOutput_in_eq_exists_of_rowidAlias state.clock state.index
    outerPosition innerPosition outer column key state.connection parameters outerTable innerTable columns namesMain
    namesIn namesExists affinity inCollation equalsCollation keyInside presentOuter presentInner alias aliased notText
  exact Sql.EquivAt.of_select_steps firstStatements secondStatements
    (firstSelect.step_of_rows (by rw [runScriptStep_output, firstResolves]; exact leftRows))
    (secondSelect.step_of_rows (by rw [runScriptStep_output, secondResolves]; exact rightRows))

end Belay.Sqlite
