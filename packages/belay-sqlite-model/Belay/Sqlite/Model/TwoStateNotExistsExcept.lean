import Belay.Sqlite.Model.TwoStateQuerySteps
import Belay.Sqlite.Model.NoFromQuerySteps
import Belay.Sqlite.Model.RowwiseExpr
import Belay.Sqlite.Model.ExceptSubqueryRun
import Belay.Sqlite.Model.ExceptCombineLaws

set_option doc.verso true

/-! The output of {lit}`SELECT 1 WHERE NOT EXISTS (SELECT … FROM before.t WHERE p EXCEPT SELECT … FROM t)` (ADR 0017,
S6), observed with the initial database. The statement has no source and three subqueries: the compound
(subquery 0), the term over the table of the initial database with the condition {lit}`p` (subquery 1), and the term
over the table of the current database (subquery 2). The output has rows when every row of the first term equals a
row of the second, and the rows of the first term are identical where they compare equal. -/

namespace Belay.Sqlite.Model

/-- The first term of the compound: the columns and the condition over the table at a position of the initial
database, in written order. -/
abbrev Resolved.initialTerm (position : Nat) (condition : Resolved.Expr) (columns : List Resolved.Expr)
    (names : List String) : Resolved.Query :=
  Resolved.Query.simple [{ kind := .inner, source := .initialTable position, condition := none }] (some condition)
    (columns.map Resolved.Output.scalar) names

/-- The second term of the compound: the columns of the table at a position of the current database, without
a condition. -/
abbrev Resolved.currentTerm (position : Nat) (columns : List Resolved.Expr) (names : List String) : Resolved.Query :=
  Resolved.Query.simple [Resolved.QuerySource.first position] none (columns.map Resolved.Output.scalar) names

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

/-- For every row-wise sources, condition and columns, every expression of the simple query is
row-wise. Proof sketch: the expressions of a simple query are its condition, those of its sources and its columns. -/
theorem Resolved.Query.simple_expressions_rowwise (sources : List Resolved.QuerySource)
    (filter : Option Resolved.Expr) (columns : List Resolved.Expr) (names : List String)
    (sourcesOk : ∀ join ∈ sources, ∀ e ∈ join.expressions, e.Rowwise) (filterOk : ∀ e ∈ filter.toList, e.Rowwise)
    (columnsOk : ∀ c ∈ columns, c.Rowwise) :
    ∀ e ∈ (Resolved.Query.simple sources filter (columns.map Resolved.Output.scalar) names).expressions, e.Rowwise := by
  intro e he
  simp only [Resolved.Query.expressions, Resolved.Query.keptExpressions, Resolved.Query.simple,
    Resolved.Output.scalars, Resolved.Output.operands, List.mem_append, List.mem_flatMap, List.mem_map,
    List.flatMap_map, List.not_mem_nil] at he
  rcases he with (he | ⟨join, member, he⟩) |
    (((((⟨column, member, he⟩ | ⟨column, member, he⟩) | ⟨_, no, _⟩) | ⟨_, no, _⟩) | ⟨_, no, _⟩) | he)
  · exact filterOk e he
  · exact sourcesOk join member e he
  · simp only [List.mem_singleton] at he
    exact he ▸ columnsOk column member
  · exact he.elim
  · exact no.elim
  · exact no.elim
  · exact no.elim
  · simp at he

/-- For every simple query whose condition and columns are row-wise, every rows and two contexts with the same bound
values, the one result is the same in both contexts. In plain words: a term of a compound gives the same rows in the
context of the statement as in the plain context of the values. Proof sketch: the rows are the columns of the rows that
{lit}`WHERE` keeps ({name}`Resolved.Query.Simple.results_eq`), and a row-wise expression evaluates in the same way in
both contexts ({name}`Resolved.Expr.Rowwise.evaluate_congr`). -/
theorem Resolved.Query.simple_results_congr (sources : List Resolved.QuerySource) (filter : Option Resolved.Expr)
    (columns : List Resolved.Expr) (names : List String) (filterOk : ∀ e ∈ filter.toList, e.Rowwise)
    (columnsOk : ∀ c ∈ columns, c.Rowwise) (first second : Resolved.EvalContext)
    (same : first.parameters = second.parameters) (rows : List (List Value)) :
    (Resolved.Query.simple sources filter (columns.map Resolved.Output.scalar) names).results first rows =
      (Resolved.Query.simple sources filter (columns.map Resolved.Output.scalar) names).results second rows := by
  have each : ∀ e : Resolved.Expr, e.Rowwise → ∀ row, e.eval first row = e.eval second row := fun e rowwise row => by
    simp only [Resolved.Expr.eval, rowwise.evaluate_congr first second row same]
  rw [(Resolved.Query.simple_isSimple _ _ _ _).results_eq, (Resolved.Query.simple_isSimple _ _ _ _).results_eq]
  have kept : Resolved.filtered first (Resolved.Query.simple sources filter (columns.map Resolved.Output.scalar) names) rows =
      Resolved.filtered second (Resolved.Query.simple sources filter (columns.map Resolved.Output.scalar) names) rows := by
    unfold Resolved.filtered
    refine List.filter_congr fun row _ => ?_
    cases filter with
    | none => rfl
    | some condition =>
      dsimp only [Resolved.Query.simple]
      simp [each condition (filterOk condition (by simp)) row]
  rw [kept]
  refine List.map_congr_left fun row _ => ?_
  dsimp only [Resolved.Query.simple]
  simp only [List.map_map, Function.comp_def]
  exact List.map_congr_left fun column member => by simp [each column (columnsOk column member) row]


/-- For every counters, values, databases, positions, tables and terms as in the statement
{name}`Resolved.notExistsExcept`, with every row of the first term a row of the second, and the rows of the first term
identical where they compare equal, subquery 0 of the context of the statement for the empty outer row has no row and no
fault. In plain words: the compound {lit}`q1 EXCEPT q2` is empty and quiet. Proof sketch: subquery 1 reads the initial
table and subquery 2 the current table ({name}`Resolved.Query.subqueryRun_simple_fields`); their results in the context of
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
  have leftFields := Resolved.Query.subqueryRun_simple_fields ctx1 database (some initial)
    (Resolved.initialTerm position condition columns names) (Resolved.Query.simple_isSimple _ _ _ _) rfl _
    (Resolved.Query.source_initialTable ctx1 _ database initial position initialTable rfl presentInitial) rfl
    (plain _ rowwise1) fun row _ e member => (rowwise1 e member).fault_none ctx1 row
  have rightFields := Resolved.Query.subqueryRun_simple_fields ctx1 database (some initial)
    (Resolved.currentTerm position columns names) (Resolved.Query.simple_isSimple _ _ _ _) rfl _
    (Resolved.Query.source_first_from ctx1 _ database (some initial) position currentTable rfl presentCurrent) rfl
    (plain _ rowwise2) fun row _ e member => (rowwise2 e member).fault_none ctx1 row
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
