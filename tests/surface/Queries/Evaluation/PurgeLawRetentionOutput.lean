import PurgeLawRetention

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the output law of the form
`SELECT 1 WHERE NOT EXISTS (SELECT … FROM before.t WHERE p EXCEPT SELECT … FROM t)` that the claim-proof pilot,
form B, deletes, proved from the laws of the parts that remain. The statement is copied from the revision of the base
form, and the definitions of the form that it needs are restated here and in `PurgeLawRetention`. -/

set_option doc.verso true

namespace PurgeLawRetention
open Belay.Sqlite.Model

/-- The subqueries of {lit}`SELECT 1 WHERE NOT EXISTS (q)`: the compound {lit}`q` (subquery 0) and its two terms
(subqueries 1 and 2). -/
abbrev Resolved.notExistsExceptSubqueries (compound : Resolved.Query) (position : Nat) (condition : Resolved.Expr)
    (columns : List Resolved.Expr) (names : List String) : List Resolved.Query :=
  [compound, Resolved.initialTerm position condition columns names, Resolved.currentTerm position columns names]

/-- The statement {lit}`SELECT 1 WHERE NOT EXISTS (q)` with the compound {lit}`q`, whose terms are the subqueries 1
and 2 of the statement. -/
abbrev Resolved.notExistsExcept (compound : Resolved.Query) (position : Nat) (condition : Resolved.Expr)
    (columns : List Resolved.Expr) (names : List String) : Resolved.Statement :=
  .query (Resolved.Query.selectOneWhere (.not (.exists 0)))
    (Resolved.notExistsExceptSubqueries compound position condition columns names)

/-- For every statement {name}`Resolved.notExistsExcept` whose compound is a plain {lit}`EXCEPT` of the subqueries 1
and 2 under the collations ({name}`Resolved.Query.PlainExcept`), every connection, values and initial database: if
the condition and each column are row-wise, the initial table and the current table are present, every row of the
first term is a row of the second term (in the context of the values), and the rows of the first term are identical
where they compare equal, then at each statement index the step of the statement, with no clock and with the initial
database, gives an output that has rows.
The statement of the base form. Proof sketch: the statement is calm, because its terms are row-wise
({name}`Resolved.Query.simple_expressions_rowwise`). The laws of the parts then apply in turn: {lit}`SELECT 1 WHERE`
({name}`resolvedStepOutput_selectOneWhere_hasRows`), {lit}`NOT EXISTS` ({name}`Resolved.Expr.truthy_notExists`), the
subqueries of the statement ({name}`Resolved.statementContext_subqueries`, {name}`Resolved.subqueryContext_subqueries`),
the compound ({name}`Resolved.Query.PlainExcept.subqueryRun`) and the read of each table
({name}`Resolved.Query.simple_subqueryRun`). The rows of a term are the same in the context of the subquery and in the
context of the values ({name}`Resolved.Query.simple_results_congr`), and the compound is empty
({name}`CompoundOperator.except_combine_eq_nil`). -/
theorem resolvedStepOutput_notExistsExcept_hasRows (index : Nat) (connection : Connection) (parameters : List Value)
    (initial : Database) (compound : Resolved.Query) (position : Nat) (condition : Resolved.Expr)
    (columns : List Resolved.Expr) (names : List String) (collations : List Collation)
    (initialTable currentTable : Table) (shape : compound.PlainExcept 1 2 collations) (conditionOk : condition.Rowwise)
    (columnsOk : ∀ c ∈ columns, c.Rowwise) (presentInitial : initial.table position = some initialTable)
    (presentCurrent : connection.state.database.table position = some currentTable)
    (subset : ∀ row ∈ (Resolved.initialTerm position condition columns names).results
        (Resolved.EvalContext.bound parameters) (Resolved.sourceRows initialTable),
      row ∈ (Resolved.currentTerm position columns names).results (Resolved.EvalContext.bound parameters)
        (Resolved.sourceRows currentTable))
    (identical : Resolved.equalRowsIdentical collations ((Resolved.initialTerm position condition columns names).results
      (Resolved.EvalContext.bound parameters) (Resolved.sourceRows initialTable)) = true) :
    (resolvedStepOutput none index connection parameters (Resolved.notExistsExcept compound position condition columns names)
      (some initial)).hasRows = true := by
  have rowwise1 := Resolved.Query.simple_expressions_rowwise
    [{ kind := .inner, source := .initialTable position, condition := none }] (some condition) columns names
    (by simp [Resolved.QuerySource.expressions]) (by simpa using conditionOk) columnsOk
  have rowwise2 := Resolved.Query.simple_expressions_rowwise [Resolved.QuerySource.first position] none columns names
    (by simp [Resolved.QuerySource.first, Resolved.QuerySource.expressions]) (by simp) columnsOk
  have plain : ∀ query : Resolved.Query, (∀ e ∈ query.expressions, e.Rowwise) →
      query.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true := fun query rowwise => by
    simp only [List.all_eq_true, Bool.not_eq_true']
    exact fun e member => (rowwise e member).calm.1
  have calm : (Resolved.notExistsExcept compound position condition columns names).Calm := by
    intro expression member
    simp only [Resolved.Statement.clockExpressions, Resolved.notExistsExceptSubqueries,
      Resolved.Query.selectOneWhere_expressions, shape.expressions, List.mem_append, List.mem_cons,
      List.mem_nil_iff, or_false, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append] at member
    rcases member with (rfl | rfl) | member | member
    · simp [Resolved.Expr.Calm, Resolved.Expr.any, Resolved.Expr.isFallibleCall, Resolved.Expr.readsClockHere,
        Resolved.Expr.readsCounterHere]
    · simp [Resolved.Expr.Calm, Resolved.Expr.any, Resolved.Expr.isFallibleCall, Resolved.Expr.readsClockHere,
        Resolved.Expr.readsCounterHere]
    · exact (rowwise1 expression member).calm
    · exact (rowwise2 expression member).calm
  have initialRead := fun context => Resolved.Query.simple_subqueryRun context connection.state.database []
    (some initial) _ (some condition) columns names
    (Resolved.Query.source_initialTable _ (Resolved.initialTerm position condition columns names) _ _ _ _ rfl
      presentInitial) rfl (plain _ rowwise1) (fun row _ e member => (rowwise1 e member).fault_none context row)
  have currentRead := fun context => Resolved.Query.simple_subqueryRun context connection.state.database []
    (some initial) _ none columns names
    (Resolved.Query.source_first_from _ (Resolved.currentTerm position columns names) _ _ _ _ rfl presentCurrent) rfl
    (plain _ rowwise2) (fun row _ e member => (rowwise2 e member).fault_none context row)
  have compoundRun : ∀ counters, ((Resolved.statementContext 0 counters parameters connection.state.database
      (Resolved.notExistsExceptSubqueries compound position condition columns names) (some initial)).subqueries 0
        []).rows = [] ∧
      ((Resolved.statementContext 0 counters parameters connection.state.database
        (Resolved.notExistsExceptSubqueries compound position condition columns names) (some initial)).subqueries 0
          []).fault = .none := by
    intro counters
    rw [Resolved.statementContext_subqueries _ _ _ _ _ _ 0 [] rfl]
    simp only [Resolved.notExistsExceptSubqueries, List.length_cons, List.length_nil]
    have left := Resolved.subqueryContext_subqueries 0 counters parameters connection.state.database
      (Resolved.notExistsExceptSubqueries compound position condition columns names) (some initial) 1 1 [] rfl
    have right := Resolved.subqueryContext_subqueries 0 counters parameters connection.state.database
      (Resolved.notExistsExceptSubqueries compound position condition columns names) (some initial) 1 2 [] rfl
    have leftRead := initialRead (Resolved.subqueryContext 0 counters parameters connection.state.database
      (Resolved.notExistsExceptSubqueries compound position condition columns names) (some initial) 1)
    have rightRead := currentRead (Resolved.subqueryContext 0 counters parameters connection.state.database
      (Resolved.notExistsExceptSubqueries compound position condition columns names) (some initial) 1)
    have sameParameters : (Resolved.subqueryContext 0 counters parameters connection.state.database
        (Resolved.notExistsExceptSubqueries compound position condition columns names) (some initial) 1).parameters =
        (Resolved.EvalContext.bound parameters).parameters := rfl
    rw [← simple_results [{ kind := .inner, source := .initialTable position, condition := none }] (some condition)
      columns names, Resolved.Query.simple_results_congr _ _ _ _ (by simpa using conditionOk) columnsOk _ _
      sameParameters] at leftRead
    rw [← simple_results [Resolved.QuerySource.first position] none columns names,
      Resolved.Query.simple_results_congr _ _ _ _ (by simp) columnsOk _ _ sameParameters] at rightRead
    have final := shape.subqueryRun _ connection.state.database (some initial) (by rw [left]; exact leftRead.2.2)
      (by rw [right]; exact rightRead.2.2) (by rw [left]; erw [leftRead.1]; exact identical)
    refine ⟨?_, final.2⟩
    rw [final.1, left, right]
    erw [leftRead.1, rightRead.1]
    exact CompoundOperator.except_combine_eq_nil collations _ _ subset
  refine (resolvedStepOutput_selectOneWhere_hasRows none index connection parameters _ _ (some initial) calm ?_).2 ?_
  · rw [Resolved.Expr.fault_not, Resolved.Expr.fault_exists]
    exact (compoundRun _).2
  · rw [Resolved.Expr.truthy_notExists]
    exact List.isEmpty_iff.2 (compoundRun _).1

#print axioms resolvedStepOutput_notExistsExcept_hasRows

end PurgeLawRetention
