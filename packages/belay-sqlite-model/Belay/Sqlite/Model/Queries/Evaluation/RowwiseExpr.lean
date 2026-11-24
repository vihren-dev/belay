import Belay.Sqlite.Model.Queries.Evaluation.StatementCalm
import Belay.Sqlite.Model.Queries.Evaluation.ExprEvalLaws
import Belay.Sqlite.Model.Queries.Evaluation.ExprCongruence
import Belay.Sqlite.Model.Queries.Evaluation.IntegerCompareLaws
import Belay.Sqlite.Model.Queries.Evaluation.QueryPlainLaws
import Belay.Sqlite.Model.Queries.Evaluation.PlainQueryRules
import Belay.Sqlite.Model.Queries.Evaluation.SelectSubqueryRules

set_option doc.verso true

/-! Expressions that read only their row and the bound values (ADR 0017, S6). A condition such as
{lit}`customer_id = $c AND expires_at < $now` names columns, literals and parameters, and combines
them with comparisons and logic. Its value does not depend on the subqueries of the context, so a
subquery that runs in a context other than the statement's context still evaluates it in the same way.
The module proves this independence, that such an expression is calm and has no fault, that no call
of a list of such expressions may fail over rows ({lit}`anyMayFail`), that each expression of a simple
query over such expressions is row-wise, and that such a simple query gives the same rows in two contexts with the
same bound values. -/

namespace Belay.Sqlite.Model.Resolved

/-- The expressions that read only their row and the bound values: columns, literals, parameters,
comparisons, {lit}`AND`, {lit}`OR`, {lit}`NOT` and {lit}`IS NULL` of such expressions. For example
{lit}`customer_id = $c AND expires_at < $now` is one; an expression with {lit}`EXISTS`, a function call
or a clock read is not. -/
inductive Expr.Rowwise : Expr → Prop where
  /-- A column. -/
  | column (position : Nat) : Rowwise (.column position)
  /-- A literal. -/
  | literal (value : Value) : Rowwise (.literal value)
  /-- A parameter. -/
  | parameter (number : Nat) : Rowwise (.parameter number)
  /-- A comparison of two such expressions. -/
  | compare (operator : Comparison) (affinity : Option Affinity) {left right : Expr} (collation : Collation) :
      Rowwise left → Rowwise right → Rowwise (.compare operator affinity left right collation)
  /-- {lit}`AND` of two such expressions. -/
  | and {left right : Expr} : Rowwise left → Rowwise right → Rowwise (.and left right)
  /-- {lit}`OR` of two such expressions. -/
  | or {left right : Expr} : Rowwise left → Rowwise right → Rowwise (.or left right)
  /-- {lit}`NOT` of such an expression. -/
  | not {operand : Expr} : Rowwise operand → Rowwise (.not operand)
  /-- {lit}`IS NULL` or {lit}`IS NOT NULL` of such an expression. -/
  | isNull {operand : Expr} (negated : Bool) : Rowwise operand → Rowwise (.isNull operand negated)

/-- Every {name}`Expr.Rowwise` expression has no node that reads beyond the row and
parameters. Proof sketch: induction on the syntax certificate, without evaluator reasoning. -/
theorem Expr.Rowwise.localReads {expression : Expr} (rowwise : expression.Rowwise) :
    expression.any Expr.readsBeyondRowAndParameters = false := by
  induction rowwise <;> simp_all [Expr.any, Expr.readsBeyondRowAndParameters]

/-- For every row-wise expression, row and two contexts with equal parameter lists, the
value/fault pair is equal. Proof sketch: {name}`Expr.Rowwise.localReads` supplies the read
boundary to {name}`Expr.evaluate_rowAndParameters`; project the pair equality. -/
theorem Expr.Rowwise.evaluate_congr {expression : Expr} (rowwise : expression.Rowwise) (first second : EvalContext)
    (row : List Value) (same : first.parameters = second.parameters) :
    expression.evaluate first row = expression.evaluate second row :=
  (expression.evaluate_rowAndParameters rowwise.localReads first second row same).1

/-- For every row-wise expression, context and row, the evaluation has no fault. Proof sketch: induction over
the expression; no form of it can fail, and the join and the softening of no faults is no fault. -/
theorem Expr.Rowwise.fault_none {expression : Expr} (rowwise : expression.Rowwise) (context : EvalContext)
    (row : List Value) : (expression.evaluate context row).2 = .none := by
  induction rowwise with
  | column | literal | parameter => simp [Expr.evaluate]
  | compare _ _ _ _ _ left right => simp [Expr.evaluate, left, right, Fault.join]
  | and _ _ left right => simp [Expr.evaluate, left, right, Fault.join, Fault.soften]
  | or _ _ left right => simp [Expr.evaluate, left, right, Fault.join, Fault.soften]
  | not _ ih => simp [Expr.evaluate, ih]
  | isNull _ _ ih => simp [Expr.evaluate, ih]

/-- For every list of row-wise expressions, context and list of rows, the test {name}`anyMayFail` is false: no call
of the expressions may fail over the rows. The readiness checks of a DELETE and of an UPDATE read this test for
their filter. Proof sketch: {name}`anyMayFail_eq_false_iff` with {name}`Expr.Rowwise.fault_none`. -/
theorem anyMayFail_of_rowwise {expressions : List Expr} (rowwise : ∀ expression ∈ expressions, expression.Rowwise)
    (context : EvalContext) (rows : List (List Value)) : anyMayFail context rows expressions = false :=
  anyMayFail_eq_false_iff.2 fun row _ expression member => (rowwise expression member).fault_none context row

/-- Every row-wise expression is calm ({name}`Expr.Calm`): it has no fallible call, reads no clock and calls
no counter function. Proof sketch: induction over the expression; the parts of each form are calm. -/
theorem Expr.Rowwise.calm {expression : Expr} (rowwise : expression.Rowwise) : expression.Calm := by
  induction rowwise with
  | column | literal | parameter =>
    simp [Expr.Calm, Expr.any, Expr.isFallibleCall, Expr.readsClockHere, Expr.readsCounterHere]
  | compare _ _ _ _ _ left right | and _ _ left right | or _ _ left right =>
    simp_all [Expr.Calm, Expr.any, Expr.isFallibleCall, Expr.readsClockHere, Expr.readsCounterHere]
  | not _ ih | isNull _ _ ih =>
    simp_all [Expr.Calm, Expr.any, Expr.isFallibleCall, Expr.readsClockHere, Expr.readsCounterHere]

/-- For every list of sources whose expressions are row-wise, every optional filter that is row-wise, every list of
row-wise columns and every list of names: each expression of the simple query ({name}`Query.simple`,
{name}`Query.expressions`) with these scalar columns is row-wise. With {name}`Expr.Rowwise.fault_none` it gives the
premise of the read rule of a simple query that no expression has a fault. Proof sketch: the expressions of a simple
query are its filter, those of its sources and its columns. -/
theorem Query.simple_expressions_rowwise (sources : List QuerySource)
    (filter : Option Expr) (columns : List Expr) (names : List String)
    (sourcesOk : ∀ join ∈ sources, ∀ e ∈ join.expressions, e.Rowwise) (filterOk : ∀ e ∈ filter.toList, e.Rowwise)
    (columnsOk : ∀ c ∈ columns, c.Rowwise) :
    ∀ e ∈ (Query.simple sources filter (columns.map Output.scalar) names).expressions, e.Rowwise := by
  intro e he
  simp only [Query.expressions, Query.keptExpressions, Query.simple,
    Output.scalars, Output.operands, List.mem_append, List.mem_flatMap, List.mem_map,
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
values, the one result is the same in both contexts. In plain words: such a query gives the same rows in any two
contexts with the same bound values, for example in the context of a subquery and in the plain context of the values.
Proof sketch: the rows are the columns of the rows that
{lit}`WHERE` keeps ({name}`Query.results_plain_unordered`), and a row-wise expression evaluates in the same way in
both contexts ({name}`Expr.Rowwise.evaluate_congr`). -/
theorem Query.simple_results_congr (sources : List QuerySource) (filter : Option Expr)
    (columns : List Expr) (names : List String) (filterOk : ∀ e ∈ filter.toList, e.Rowwise)
    (columnsOk : ∀ c ∈ columns, c.Rowwise) (first second : EvalContext)
    (same : first.parameters = second.parameters) (rows : List (List Value)) :
    (Query.simple sources filter (columns.map Output.scalar) names).results first rows =
      (Query.simple sources filter (columns.map Output.scalar) names).results second rows := by
  have each : ∀ e : Expr, e.Rowwise → ∀ row, e.eval first row = e.eval second row := fun e rowwise row => by
    simp only [Expr.eval, rowwise.evaluate_congr first second row same]
  rw [Query.results_plain_unordered first rfl rfl rfl rfl rfl rfl,
    Query.results_plain_unordered second rfl rfl rfl rfl rfl rfl]
  have kept : filtered first (Query.simple sources filter (columns.map Output.scalar) names) rows =
      filtered second (Query.simple sources filter (columns.map Output.scalar) names) rows := by
    unfold filtered
    refine List.filter_congr fun row _ => ?_
    cases filter with
    | none => rfl
    | some condition =>
      dsimp only [Query.simple]
      simp [each condition (filterOk condition (by simp)) row]
  rw [kept]
  refine List.map_congr_left fun row _ => ?_
  dsimp only [Query.rowOutput, Query.simple]
  simp only [List.map_map, Function.comp_def]
  exact List.map_congr_left fun column member => by simp [each column (columnsOk column member) row]

end Belay.Sqlite.Model.Resolved
