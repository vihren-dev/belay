import SelectOneWhereSupport

set_option doc.verso true

/-! Support of the claims about {lit}`SELECT 1 WHERE c(SELECT count(*) FROM t WHERE p)` over every
database, through the phase rules of ADR 0027: the subquery run rule
({lit}`Resolved.Query.subqueryRun_of_faultless`), the ungrouped aggregate rule
({lit}`Resolved.records_ungrouped`), the one-subquery context rule
({lit}`Resolved.Expr.evaluate_statement_one`) and the claims of {lit}`SELECT 1 WHERE c`
({lit}`whereOne_claims`). The fixtures {lit}`ClaimsCount`, {lit}`ClaimsUniqueLookup`,
{lit}`CustomerInsertQueries`, {lit}`AccountSignupQueries` and {lit}`ExpansionCountQueries` use it. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- For every database with a table at a position under some name, values, calm condition {lit}`p`
and result name: the run of {lit}`SELECT count(*) FROM t WHERE p` as a subquery with the values for
the row with no cells is the one row with the number of rows of the table for which {lit}`p` is true
({name}`Resolved.countMatching`), with no fault and certain rows. Proof sketch:
{name}`Resolved.Query.subqueryRun_of_faultless` with the scan of the table; the one group of all the
kept rows ({name}`Resolved.records_ungrouped`) gives one record, which every order and window keep. -/
theorem countOne_run (db : Database) (parameters : List Value) (name : Identifier) (position : Nat)
    (table : CatalogTable) (condition : Option Resolved.Expr) (text : String)
    (found : db.raw.catalog.findTable name = some (position, table))
    (calm : ∀ expression ∈ condition.toList, expression.Calm) :
    (Resolved.Query.countOf [.first position] condition text).subqueryRun (Resolved.EvalContext.bound parameters)
        db.raw [] =
      Resolved.SubqueryRun.count (Resolved.countMatching (Resolved.EvalContext.bound parameters) condition
        { shape := table, rows := db.raw.rows.getD position [] }) := by
  have plain : (Resolved.Query.countOf [.first position] condition text).expressions.all
      (!·.any Resolved.Expr.isFallibleCall) = true := by
    rw [Resolved.Query.countOf_expressions]
    exact List.all_eq_true.mpr fun expression member => by
      have inside : expression ∈ condition.toList := by
        simpa [Resolved.QuerySource.first, Resolved.QuerySource.expressions] using member
      simp [(calm expression inside).1]
  have run := Resolved.Query.subqueryRun_of_faultless (Resolved.EvalContext.bound parameters) db.raw [] none
    rfl rfl rfl
    (Resolved.Query.sourceAfter_first _ db.raw none _ position _ [] rfl
      (Database.table_of_findTable db.raw _ position table found)) rfl plain
    (fun row _ expression member => Resolved.Expr.fault_of_plain _ (Resolved.EvalContext.bound_quiet parameters)
      row expression (by simpa using List.all_eq_true.mp plain expression member))
    (by simp [Resolved.Query.fails, Resolved.Query.countOf, Resolved.Aggregate.fails])
    (by simp [Resolved.Query.distinctCertain, Resolved.Query.countOf])
  have records := fun rows => Resolved.records_ungrouped (Resolved.EvalContext.bound parameters)
    (query := Resolved.Query.countOf [.first position] condition text) rfl rfl rfl rows
  rw [run]
  simp only [Resolved.Query.results, Resolved.Query.uniqueRecords, Resolved.Query.windowCertain, records]
  simp [Resolved.SubqueryRun.count, Resolved.certainCut, Resolved.Query.groupRecord, Resolved.Query.countOf,
    Resolved.Aggregate.eval, Resolved.countMatching, Resolved.filtered, Resolved.outerCells, Resolved.stableSort,
    Resolved.insertStable]

/-- For every number, the context of the values with the run of a count ({name}`Resolved.SubqueryRun.count`)
as its one subquery is quiet: each subquery gives no fault and certain rows. Proof sketch: the count and
the empty run past it have no fault and certain rows by definition. -/
theorem withCount_quiet (parameters : List Value) (count : Nat) :
    ((Resolved.EvalContext.bound parameters).withRuns [Resolved.SubqueryRun.count count]).Quiet := by
  intro index row
  cases index <;> exact ⟨rfl, rfl, rfl⟩

/-- For every script of one statement {lit}`SELECT 1 WHERE c` with values and the one subquery
{lit}`SELECT count(*) FROM t WHERE p`, database with the table {lit}`t` at a position, and calm
conditions {lit}`c` and {lit}`p` that resolve as for {name}`resolveStatement_selectOne_count`, with
{lit}`n` the number of rows of the table for which {lit}`p` is true ({name}`Resolved.countMatching`)
and {lit}`c` evaluated with {lit}`n` as the value of the subquery:

* {name}`Holds` holds exactly when {lit}`c` is true,
* {name (full := Belay.Sqlite.Empty)}`Empty` holds exactly when {lit}`c` is not true, and
* {name}`Fails` does not hold.

The table reference names no schema and has no indexed query and no arguments. Proof sketch:
{name}`whereOne_claims` with the resolution, {name}`countOne_run` for the subquery and
{name}`Resolved.Expr.evaluate_statement_one` for {lit}`c`. -/
theorem whereCount_claims {script : Script} {isQuery : script.isQuery = true} {db : Database}
    {reference : Syntax.TableReference} {subFilter : Option Syntax.Expr} {mainFilter : Syntax.Expr}
    {parameters : List Value} {position : Nat} {table : CatalogTable} {subCondition : Option Resolved.Expr}
    {mainCondition : Resolved.Expr} {name : String} {text : String}
    (head : script.statements = [(.select [.expression (.numeric "1") none "1"] none [] (some mainFilter) [] [] none
      none [Syntax.Subquery.mk [.expression (.callStar name) none text] (some reference) [] subFilter [] [] none none
        none none false none none] none false none, parameters)])
    (count : normalizeIdentifier name = "count") (namedSource : reference.query = none)
    (current : reference.schema = none) (arguments : reference.arguments = none)
    (found : db.raw.catalog.findTable reference.table = some (position, table))
    (subResolves : FilterResolves runContext.profile.dqsDml (tableScope db.raw.catalog reference position table) []
      subFilter subCondition { current := some 0 })
    (mainResolves : ∀ lowest : Option Nat, FilterResolves runContext.profile.dqsDml [] [] (some mainFilter)
      (some mainCondition) { later := [countShape lowest] })
    (mainCalm : mainCondition.Calm) (subCalm : ∀ expression ∈ subCondition.toList, expression.Calm) :
    (Holds script db isQuery ↔ Resolved.truthy (mainCondition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.count (Resolved.countMatching (Resolved.EvalContext.bound parameters) subCondition
          { shape := table, rows := db.raw.rows.getD position [] })]) []) = true) ∧
      (Belay.Sqlite.Empty script db isQuery ↔ Resolved.truthy (mainCondition.eval
        ((Resolved.EvalContext.bound parameters).withRuns [Resolved.SubqueryRun.count (Resolved.countMatching
          (Resolved.EvalContext.bound parameters) subCondition { shape := table, rows := db.raw.rows.getD position [] })])
        []) = false) ∧
      ¬ Fails script db isQuery := by
  have resolved := resolveStatement_selectOne_count runContext (db.raw.connection Env.default.counters).resolveState
    reference subFilter mainFilter position table subCondition mainCondition name text count namedSource current
    arguments found subResolves mainResolves mainCalm.1
  have same := Resolved.Expr.evaluate_statement_one parameters db.raw
    (Resolved.Query.countOf [.first position] subCondition text) mainCondition
  rw [countOne_run db parameters reference.table position table subCondition text found subCalm] at same
  have value := congrArg Prod.fst same
  obtain ⟨holds, empty, notFails⟩ := whereOne_claims (isQuery := isQuery) _ parameters head db mainCondition _
    resolved (Resolved.Statement.Calm.selectOne_count position _ subCondition text mainCalm subCalm)
    (by rw [same]; exact Resolved.Expr.fault_of_plain _ (withCount_quiet _ _) [] mainCondition mainCalm.1)
  exact ⟨holds.trans (by rw [Resolved.Expr.eval, Resolved.Expr.eval, value]),
    empty.trans (by rw [Resolved.Expr.eval, Resolved.Expr.eval, value]), notFails⟩

#print axioms countOne_run
#print axioms whereCount_claims
