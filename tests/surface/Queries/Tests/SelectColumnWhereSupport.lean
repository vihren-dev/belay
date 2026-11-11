import SelectOneWhereSupport

set_option doc.verso true

/-! Support of the claims about {lit}`SELECT 1 WHERE c(SELECT e FROM t WHERE p)` over every database,
where {lit}`c` reads the one column of the subquery, as {lit}`$x IN (SELECT id FROM t)` does, through
the phase rules of ADR 0027: the subquery run rule ({lit}`Resolved.Query.subqueryRun_of_faultless`),
the unordered result rule ({lit}`Resolved.Query.results_plain_unordered`), the one-subquery context
rule ({lit}`Resolved.Expr.evaluate_statement_one`), the rule that a condition without a scalar
subquery does not read the certainty of a first row ({lit}`Resolved.Expr.evaluate_certainFirst`) and
the claims of {lit}`SELECT 1 WHERE c` ({lit}`whereOne_claims`). The fixture {lit}`ClaimsIn` uses it. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The rows that {lit}`SELECT e FROM t WHERE p` gives over the rows of a table in a context: the value
of {lit}`e` for each row for which {lit}`p` is true, one value in a row, in scan order. -/
def columnValues (context : Resolved.EvalContext) (condition : Option Resolved.Expr) (value : Resolved.Expr)
    (table : Table) : List (List Value) :=
  ((Resolved.sourceRows table).filter fun row => condition.all fun expression =>
    Resolved.truthy (expression.eval context row)).map fun row => [value.eval context row]

/-- The run of {lit}`SELECT e FROM t WHERE p` as a subquery with the values, with its first row marked
certain: the rows {name}`columnValues`, no fault and certain rows. -/
abbrev columnRun (parameters : List Value) (condition : Option Resolved.Expr) (value : Resolved.Expr)
    (table : Table) : Resolved.SubqueryRun :=
  { rows := columnValues (Resolved.EvalContext.bound parameters) condition value table, fault := .none }

/-- For every database with a table at a position under some name, values, calm condition {lit}`p`,
calm expression {lit}`e` and names: the run of {lit}`SELECT e FROM t WHERE p` as a subquery with the
values for the row with no cells is {name}`columnRun` (the rows {name}`columnValues`, no fault and
certain rows) once its first row is marked certain. Proof sketch: {name}`Resolved.Query.subqueryRun_of_faultless` with the scan
of the table, then {name}`Resolved.Query.results_plain_unordered`; without a limit the cut at the start
and at the end are certain. -/
theorem columnOne_run (db : Database) (parameters : List Value) (name : Identifier) (position : Nat)
    (table : CatalogTable) (condition : Option Resolved.Expr) (value : Resolved.Expr) (names : List String)
    (found : db.raw.catalog.findTable name = some (position, table))
    (calm : ∀ expression ∈ condition.toList, expression.Calm) (valueCalm : value.Calm) :
    ((Resolved.Query.simple [.first position] condition [.scalar value] names).subqueryRun
        (Resolved.EvalContext.bound parameters) db.raw []).certainFirst =
      columnRun parameters condition value { shape := table, rows := db.raw.rows.getD position [] } := by
  have plain := (Resolved.Statement.Calm.selectOne_subquery position _ condition value names
    (Resolved.Expr.calm_exists 0) calm valueCalm).subquery_plain (List.mem_singleton_self _)
  have run := Resolved.Query.subqueryRun_of_faultless (Resolved.EvalContext.bound parameters) db.raw [] none
    rfl rfl rfl
    (Resolved.Query.sourceAfter_first _ db.raw none _ position _ [] rfl
      (Database.table_of_findTable db.raw _ position table found)) rfl plain
    (fun row _ expression member => Resolved.Expr.fault_of_plain _ (Resolved.EvalContext.bound_quiet parameters)
      row expression (by simpa using List.all_eq_true.mp plain expression member))
    (by simp [Resolved.Query.fails, Resolved.Query.simple])
    (by simp [Resolved.Query.distinctCertain, Resolved.Query.simple])
  rw [run, Resolved.Query.results_plain_unordered _ rfl rfl rfl rfl rfl rfl]
  simp [Resolved.SubqueryRun.certainFirst, Resolved.Query.windowCertain, Resolved.certainCut, columnValues,
    Resolved.filtered, Resolved.Query.rowOutput, Resolved.outerCells, Resolved.Query.simple]

/-- For every script of one statement {lit}`SELECT 1 WHERE c` with values and the one subquery
{lit}`SELECT e FROM t WHERE p`, database with the table {lit}`t` at a position, {lit}`e` that is no
function call and no aggregate and resolves in the scope of the table, and calm {lit}`c`, {lit}`p` and
{lit}`e` that resolve as for {name}`resolveStatement_selectOne_scalar`, where {lit}`c` reads no scalar
subquery, with {lit}`c` evaluated with {name}`columnRun` as the run of the subquery:

* {name}`Holds` holds exactly when {lit}`c` is true,
* {name (full := Belay.Sqlite.Empty)}`Empty` holds exactly when {lit}`c` is not true, and
* {name}`Fails` does not hold.

The table reference names no schema and has no indexed query and no arguments. Proof sketch:
{name}`whereOne_claims` with the resolution; {name}`Resolved.Expr.evaluate_statement_one`,
{name}`Resolved.Expr.evaluate_certainFirst` and {name}`columnOne_run` give the value of {lit}`c`. -/
theorem whereColumn_claims {script : Script} {isQuery : script.isQuery = true} {db : Database}
    {reference : Syntax.TableReference} {subFilter : Option Syntax.Expr} {mainFilter : Syntax.Expr}
    {parameters : List Value} {position : Nat} {table : CatalogTable} {subCondition : Option Resolved.Expr}
    {mainCondition : Resolved.Expr} {value : Syntax.Expr} {expression : Resolved.Expr}
    {affinity : Option Affinity} {text : String}
    (head : script.statements = [(.select [.expression (.numeric "1") none "1"] none [] (some mainFilter) [] [] none
      none [Syntax.Subquery.mk [.expression value none text] (some reference) [] subFilter [] [] none none none none
        false none none] none false none, parameters)])
    (notCall : value.isCall = false) (noAggregate : value.aggregateCalls.isEmpty = true)
    (namedSource : reference.query = none) (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : db.raw.catalog.findTable reference.table = some (position, table))
    (operand : resolveOperand runContext.profile.dqsDml (tableScope db.raw.catalog reference position table)
      { current := some 0 } false value = .ok (expression, affinity))
    (subResolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (mainResolves : ∀ lowest : Option Nat,
      FilterResolves runContext.profile.dqsDml [] [] (some mainFilter) (some mainCondition)
        { later := [scalarShape affinity value.explicitCollation (value.columnCollation
          (tableScope db.raw.catalog reference position table)) lowest
          (value.originType (tableScope db.raw.catalog reference position table) { current := some 0 })] })
    (noScalar : mainCondition.any (· matches .subquery _) = false) (mainCalm : mainCondition.Calm)
    (subCalm : ∀ expression ∈ subCondition.toList, expression.Calm) (valueCalm : expression.Calm) :
    (Holds script db isQuery ↔ Resolved.truthy (mainCondition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [columnRun parameters subCondition expression
          { shape := table, rows := db.raw.rows.getD position [] }]) []) = true) ∧
      (Belay.Sqlite.Empty script db isQuery ↔ Resolved.truthy (mainCondition.eval
        ((Resolved.EvalContext.bound parameters).withRuns [columnRun parameters subCondition expression
          { shape := table, rows := db.raw.rows.getD position [] }])
        []) = false) ∧
      ¬ Fails script db isQuery := by
  have resolved := resolveStatement_selectOne_scalar runContext (db.raw.connection Env.default.counters).resolveState
    reference value text subFilter mainFilter position table subCondition mainCondition expression affinity notCall
    noAggregate namedSource current arguments found operand valueCalm.1 subResolves mainResolves mainCalm.1
  have same : ∀ names, mainCondition.evaluate (Resolved.EvalContext.statement parameters db.raw
      [Resolved.Query.simple [.first position] subCondition [.scalar expression] names]) [] =
      mainCondition.evaluate ((Resolved.EvalContext.bound parameters).withRuns
        [columnRun parameters subCondition expression
          { shape := table, rows := db.raw.rows.getD position [] }]) [] := by
    intro names
    rw [Resolved.Expr.evaluate_statement_one, ← (Resolved.Expr.evaluate_certainFirst _ [] mainCondition noScalar).1]
    refine ((Resolved.Expr.evaluate_withSubqueries _ [] _ (fun index => ?_) mainCondition).1).symm
    cases index with
    | zero =>
      exact columnOne_run db parameters reference.table position table subCondition expression _ found subCalm
        valueCalm
    | succ later => rfl
  have valueEq := fun names => congrArg Prod.fst (same names)
  obtain ⟨holds, empty, notFails⟩ := whereOne_claims (isQuery := isQuery) _ parameters head db mainCondition _
    resolved (Resolved.Statement.Calm.selectOne_subquery position _ subCondition expression _ mainCalm subCalm valueCalm)
    (by rw [same]; exact Resolved.Expr.fault_of_plain _ (withRows_quiet _ _) [] mainCondition mainCalm.1)
  exact ⟨holds.trans (by rw [Resolved.Expr.eval, Resolved.Expr.eval, valueEq]),
    empty.trans (by rw [Resolved.Expr.eval, Resolved.Expr.eval, valueEq]), notFails⟩

#print axioms columnOne_run
#print axioms whereColumn_claims
