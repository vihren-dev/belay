import Belay.Sqlite.Model.Queries.Evaluation.SelectSubqueryRules
import Belay.Sqlite.Model.Queries.Evaluation.RowwiseExpr
import Belay.Sqlite.Model.Queries.Evaluation.ExceptSubqueryRun
import Belay.Sqlite.Model.Queries.Evaluation.ExceptCombineLaws

set_option doc.verso true

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
{lit}`WHERE` keeps ({name}`Resolved.Query.results_plain_unordered`), and a row-wise expression evaluates in the same way in
both contexts ({name}`Resolved.Expr.Rowwise.evaluate_congr`). -/
theorem Resolved.Query.simple_results_congr (sources : List Resolved.QuerySource) (filter : Option Resolved.Expr)
    (columns : List Resolved.Expr) (names : List String) (filterOk : ∀ e ∈ filter.toList, e.Rowwise)
    (columnsOk : ∀ c ∈ columns, c.Rowwise) (first second : Resolved.EvalContext)
    (same : first.parameters = second.parameters) (rows : List (List Value)) :
    (Resolved.Query.simple sources filter (columns.map Resolved.Output.scalar) names).results first rows =
      (Resolved.Query.simple sources filter (columns.map Resolved.Output.scalar) names).results second rows := by
  have each : ∀ e : Resolved.Expr, e.Rowwise → ∀ row, e.eval first row = e.eval second row := fun e rowwise row => by
    simp only [Resolved.Expr.eval, rowwise.evaluate_congr first second row same]
  rw [Resolved.Query.results_plain_unordered first rfl rfl rfl rfl rfl rfl,
    Resolved.Query.results_plain_unordered second rfl rfl rfl rfl rfl rfl]
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
  dsimp only [Resolved.Query.rowOutput, Resolved.Query.simple]
  simp only [List.map_map, Function.comp_def]
  exact List.map_congr_left fun column member => by simp [each column (columnsOk column member) row]

end Belay.Sqlite.Model
