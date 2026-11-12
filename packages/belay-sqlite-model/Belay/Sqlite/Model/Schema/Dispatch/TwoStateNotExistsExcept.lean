import Belay.Sqlite.Model.Schema.Dispatch.TwoStateQuerySteps
import Belay.Sqlite.Model.Schema.Dispatch.SelectSubqueryRules
import Belay.Sqlite.Model.Schema.Dispatch.ExceptSubqueryRun
import Belay.Sqlite.Model.Queries.Evaluation.TwoStateNotExistsExcept

set_option doc.verso true

/-! The output of {lit}`SELECT 1 WHERE NOT EXISTS (SELECT … FROM before.t WHERE p EXCEPT SELECT … FROM t)` (ADR 0017,
S6), observed with the initial database. The statement has no source and three subqueries: the compound
(subquery 0), the term over the table of the initial database with the condition {lit}`p` (subquery 1), and the term
over the table of the current database (subquery 2). The output has rows when every row of the first term equals a
row of the second, and the rows of the first term are identical where they compare equal. -/

namespace Belay.Sqlite.Model

/-- For every counters, values, databases, positions, tables and terms as in the statement
{name}`Resolved.notExistsExcept`, with every row of the first term a row of the second, and the rows of the first term
identical where they compare equal, subquery 0 of the context of the statement for the empty outer row has no row and no
fault. In plain words: the compound {lit}`q1 EXCEPT q2` is empty and quiet. Proof sketch: subquery 1 reads the initial
table and subquery 2 the current table ({name}`Resolved.Query.subqueryRun_of_faultless`); their results in the context of
the subqueries are the results in the context of the values ({name}`Resolved.Query.simple_results_congr`);
{name}`Resolved.Query.PlainExcept.subqueryRun` gives the rows of the compound, which
{name}`CompoundOperator.except_combine_eq_nil` shows empty. -/
theorem Resolved.notExistsExcept_context_zero (counters : Counters) (parameters : List Value) (database initial : Database)
    (compound : Resolved.Query) (position : Nat) (condition : Resolved.Expr) (columns : List Resolved.Expr)
    (names : List String) (collations : List Collation) (initialTable currentTable : Table)
    (shape : compound.PlainExcept 1 2 collations) (conditionOk : condition.Rowwise)
    (columnsOk : ∀ c ∈ columns, c.Rowwise) (presentInitial : initial.table position = some initialTable)
    (presentCurrent : database.table position = some currentTable)
    (subset : ∀ row ∈ (Resolved.initialTerm position condition columns names).results
        (Resolved.EvalContext.bound parameters) (sourceRows initialTable),
      row ∈ (Resolved.currentTerm position columns names).results (Resolved.EvalContext.bound parameters)
        (sourceRows currentTable))
    (identical : equalRowsIdentical collations ((Resolved.initialTerm position condition columns names).results
      (Resolved.EvalContext.bound parameters) (sourceRows initialTable)) = true) :
    ((Resolved.statementContext 0 counters parameters database
      (Resolved.notExistsExceptSubqueries compound position condition columns names) (some initial)).subqueries 0 []).rows = [] ∧
    ((Resolved.statementContext 0 counters parameters database
      (Resolved.notExistsExceptSubqueries compound position condition columns names) (some initial)).subqueries 0 []).fault = .none := by
  have rowwise1 := Resolved.Query.simple_expressions_rowwise [{ kind := .inner, source := .initialTable position, condition := none }]
    (some condition) columns names (by simp [Resolved.QuerySource.expressions]) (by simpa using conditionOk) columnsOk
  have rowwise2 := Resolved.Query.simple_expressions_rowwise [Resolved.QuerySource.first position]
    none columns names (by simp [Resolved.QuerySource.first, Resolved.QuerySource.expressions]) (by simp) columnsOk
  let ctx1 := subqueryContext 0 counters parameters database
    (Resolved.notExistsExceptSubqueries compound position condition columns names) (some initial) 1
  let ctx2 := subqueryContext 0 counters parameters database
    (Resolved.notExistsExceptSubqueries compound position condition columns names) (some initial) 2
  have leftRun : ctx2.subqueries 1 [] = (Resolved.initialTerm position condition columns names).subqueryRun ctx1 database []
    (some initial) := rfl
  have rightRun : ctx2.subqueries 2 [] = (Resolved.currentTerm position columns names).subqueryRun ctx1 database []
    (some initial) := rfl
  have plain : ∀ query : Resolved.Query, (∀ e ∈ query.expressions, e.Rowwise) →
      query.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true := fun query rowwise => by
    simp only [List.all_eq_true, Bool.not_eq_true']
    exact fun e member => (rowwise e member).calm.1
  have fields : ∀ {query : Resolved.Query} {source : Resolved.SourceRows}, query.compound = none →
      query.limitParameter = none → query.offsetParameter = none → query.outer = 0 →
      query.source ctx1 database (some initial) = some source → source.fault = .none →
      query.expressions.all (!·.any Resolved.Expr.isFallibleCall) = true →
      (∀ row ∈ [] :: source.rows, ∀ e ∈ query.expressions, (e.evaluate ctx1 row).2 = .none) →
      query.fails ctx1 source.rows = false → query.distinctCertain ctx1 source.rows = true →
      (query.subqueryRun ctx1 database [] (some initial)).rows = query.results ctx1 source.rows ∧
        (query.subqueryRun ctx1 database [] (some initial)).fault = .none ∧
        (query.subqueryRun ctx1 database [] (some initial)).ending = .done := by
    intro query source single limitParameter offsetParameter outer found clean plainQuery faultless noOverflow distinct
    rw [Resolved.Query.subqueryRun_of_faultless ctx1 database [] (some initial) single limitParameter offsetParameter
      (by rw [Resolved.Query.sourceAfter_of_outer_zero _ _ _ outer]; exact found) clean plainQuery faultless noOverflow
      distinct]
    exact ⟨rfl, rfl, rfl⟩
  have leftFields := fields (query := Resolved.initialTerm position condition columns names) rfl rfl rfl rfl
    (Resolved.Query.source_initialTable ctx1 _ database initial position initialTable rfl presentInitial) rfl
    (plain _ rowwise1) (fun row _ e member => (rowwise1 e member).fault_none ctx1 row) rfl rfl
  have rightFields := fields (query := Resolved.currentTerm position columns names) rfl rfl rfl rfl
    (Resolved.Query.source_first_from ctx1 _ database (some initial) position currentTable rfl presentCurrent) rfl
    (plain _ rowwise2) (fun row _ e member => (rowwise2 e member).fault_none ctx1 row) rfl rfl
  rw [← leftRun] at leftFields
  rw [← rightRun] at rightFields
  have sameParameters : ctx1.parameters = (Resolved.EvalContext.bound parameters).parameters := rfl
  rw [Resolved.Query.simple_results_congr _ _ _ _ (by simpa using conditionOk) columnsOk ctx1 _ sameParameters] at leftFields
  rw [Resolved.Query.simple_results_congr _ _ _ _ (by simp) columnsOk ctx1 _ sameParameters] at rightFields
  have final := shape.subqueryRun ctx2 database (some initial) leftFields.2.2 rightFields.2.2
    (by rw [leftFields.1]; exact identical)
  have zeroRun : (Resolved.statementContext 0 counters parameters database
      (Resolved.notExistsExceptSubqueries compound position condition columns names) (some initial)).subqueries 0 [] =
      compound.subqueryRun ctx2 database [] (some initial) := rfl
  rw [zeroRun]
  refine ⟨?_, final.2⟩
  rw [final.1, leftFields.1, rightFields.1]
  exact CompoundOperator.except_combine_eq_nil collations _ _ subset

end Belay.Sqlite.Model
