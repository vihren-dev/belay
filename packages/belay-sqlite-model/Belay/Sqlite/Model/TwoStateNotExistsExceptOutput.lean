import Belay.Sqlite.Model.TwoStateNotExistsExcept

set_option doc.verso true

/-! The output of {lit}`SELECT 1 WHERE NOT EXISTS (SELECT … FROM before.t WHERE p EXCEPT SELECT … FROM t)` (ADR 0017,
S6), observed with the initial database ({name}`Belay.Sqlite.Model.Resolved.notExistsExcept`). The statement has
rows when the compound is empty: every row of the first term, which reads the initial table, is a row of the second
term, which reads the current table. -/

namespace Belay.Sqlite.Model

/-- For every statement {name}`Resolved.notExistsExcept` whose compound has the shape of
{name}`Resolved.Query.PlainExcept` and whose condition and columns are row-wise ({name}`Resolved.Expr.Rowwise`), the
statement is calm. Proof sketch: the
expressions of the statement are those of the main query ({lit}`NOT EXISTS` and the literal one), the compound (none)
and the two terms, which are row-wise and so calm. -/
theorem Resolved.notExistsExcept_calm (compound : Resolved.Query) (position : Nat) (condition : Resolved.Expr)
    (columns : List Resolved.Expr) (names : List String) (collations : List Collation)
    (shape : compound.PlainExcept 1 2 collations) (conditionOk : condition.Rowwise)
    (columnsOk : ∀ c ∈ columns, c.Rowwise) :
    (Resolved.notExistsExcept compound position condition columns names).Calm := by
  have rowwise1 := Resolved.Query.simple_expressions_rowwise
    [{ kind := .inner, source := .initialTable position, condition := none }] (some condition) columns names
    (by simp [Resolved.QuerySource.expressions]) (by simpa using conditionOk) columnsOk
  have rowwise2 := Resolved.Query.simple_expressions_rowwise [Resolved.QuerySource.first position] none columns names
    (by simp [Resolved.QuerySource.first, Resolved.QuerySource.expressions]) (by simp) columnsOk
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

/-- For every statement {name}`Resolved.notExistsExcept` as in {name}`Resolved.notExistsExcept_calm`, every connection,
values and initial database such that the initial table and the current table are present, every row of the first
term is a row of the second term (in the context of the values), and the rows of the first term are identical where
they compare equal: the output of the step of the statement, observed with the initial database, has rows. In plain
words: the query {lit}`SELECT 1 WHERE NOT EXISTS (… EXCEPT …)` returns its row when the compound is empty, and the
compound is empty when each row of the first term, which reads the initial table, is a row of the second term, which
reads the current table. Proof sketch: subquery 0 of the context has no row and no fault
({name}`Resolved.notExistsExcept_context_zero`), so {lit}`NOT EXISTS` is true over the one row with no cells and has no
fault, so the run of the query has no fault ({name}`Resolved.Query.run_of_faultless`), {lit}`WHERE` keeps the row
({name}`Resolved.Query.results_eq_nil_iff_plain`), and {name}`resolvedStepOutput_query_hasRows_of_clean_from` gives
the rows. -/
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
  have calm := Resolved.notExistsExcept_calm compound position condition columns names collations shape conditionOk columnsOk
  obtain ⟨empty, quiet⟩ := Resolved.notExistsExcept_context_zero
    (connection.state.counters.view (Resolved.notExistsExcept compound position condition columns names).counterReads)
    parameters connection.state.database initial compound position condition columns names collations initialTable
    currentTable shape conditionOk columnsOk presentInitial presentCurrent subset identical
  have value : ((Resolved.Expr.not (.exists 0)).evaluate
      (connection.queryContextFrom parameters (Resolved.Query.selectOneWhere (.not (.exists 0)))
        (Resolved.notExistsExceptSubqueries compound position condition columns names) initial) []) =
      (.integer 1, .none) := by
    simp [Resolved.Expr.evaluate, Connection.queryContextFrom, empty, quiet, truth, Value.not, Value.isNull, Resolved.truthy]
  have faultless : ∀ row ∈ [] :: [[]], ∀ expression ∈ (Resolved.Query.selectOneWhere (.not (.exists 0))).expressions,
      (expression.evaluate (connection.queryContextFrom parameters (Resolved.Query.selectOneWhere (.not (.exists 0)))
        (Resolved.notExistsExceptSubqueries compound position condition columns names) initial) row).2 = .none := by
    intro row member expression inside
    have : row = [] := by simpa using member
    subst this
    exact Resolved.Query.selectOneWhere_faultless _ _ (by rw [value]) expression inside
  refine resolvedStepOutput_query_hasRows_of_clean_from index connection parameters _ _ _ initial
    { rows := [[]], width := 0, fault := .none } _ calm (Resolved.Query.source_noFrom_from _ _ _ _ rfl)
    (Resolved.Query.bindWindow_literal _ _ rfl rfl)
    (Resolved.Query.run_of_faultless _ rfl rfl rfl calm.query_plain faultless rfl rfl) rfl rfl rfl rfl ?_
  rw [Ne, Resolved.Query.results_eq_nil_iff_plain _ rfl rfl rfl rfl (by simp [Resolved.Query.simple])]
  intro empty
  have kept := (Resolved.mem_filtered _ (Resolved.Query.selectOneWhere (.not (.exists 0))) [[]] []).mpr
    ⟨by simp, by
      change Resolved.truthy (((Resolved.Expr.not (.exists 0)).evaluate
        (connection.queryContextFrom parameters (Resolved.Query.selectOneWhere (.not (.exists 0)))
          (Resolved.notExistsExceptSubqueries compound position condition columns names) initial) []).1) = true
      rw [value]
      rfl⟩
  rw [empty] at kept
  simp at kept

end Belay.Sqlite.Model
