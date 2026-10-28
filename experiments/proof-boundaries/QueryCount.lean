import QuerySemantic
import Belay.Sqlite.Model.CountSubqueryOutput

set_option doc.verso true

namespace ProofBoundaries
open Belay.Sqlite Belay.Sqlite.Model

section
variable (index : Nat) (connection : Connection) (parameters : List Value)
  (condition : Resolved.Expr) (position : Nat) (table : Table)
  (subCondition : Option Resolved.Expr) (name : String)
  (present : connection.state.database.table position = some table)
  (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere condition)
    [Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition name]).Calm)
include present calm

/-- For every count-subquery statement with the original table and calmness premises,
the exact output contains all possible outer results, and its condition reads the count
of matching table rows. Proof sketch: obtain the subquery context once, then apply the
shared simple-query output law to the one empty source row. -/
theorem count_semantics :
    let query := Resolved.Query.selectOneWhere condition
    let subqueries := [Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition name]
    let context := connection.queryContext parameters query subqueries
    resolvedStepOutput none index connection parameters (.query query subqueries) =
        Output.ofResults (query.possibleResults context [[]]) ∧
      condition.eval context [] = condition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.count (Resolved.countMatching (Resolved.EvalContext.bound parameters) subCondition table)]) [] := by
  dsimp only
  have semantic := connection.queryContext_selectOne parameters condition _ _ calm
    (connection.queryContext_countSubquery_runs parameters _ position table subCondition name present calm)
    (fun run member => by simp only [List.mem_singleton] at member; rw [member]; exact Resolved.SubqueryRun.count_quiet _)
  refine ⟨?_, semantic.2⟩
  have output := simple_output index connection parameters (Resolved.Query.selectOneWhere condition) _
    (Resolved.Query.simple_isSimple _ _ _ _) { rows := [[]], width := 0, fault := .none } calm
    (Resolved.Query.source_none _ _ _ rfl) (fun row member expression inside => by
      have empty : row = [] := by simpa using member
      subst empty
      exact Resolved.Query.selectOneWhere_faultless _ condition semantic.1 expression inside)
  simpa using output

/-- Under the original count-query premises, the output has rows exactly when the
condition is true with the matching count. Proof sketch: project the semantic certificate
through the possible-results row law and rewrite its single condition value. -/
theorem count_hasRows :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition name])).hasRows = true ↔
      Resolved.truthy (condition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.count (Resolved.countMatching (Resolved.EvalContext.bound parameters) subCondition table)]) []) = true := by
  obtain ⟨output, value⟩ := count_semantics index connection parameters condition position table subCondition name present calm
  rw [output, Output.hasRows_possibleResults, (Resolved.Query.simple_isSimple _ _ _ _).results_ne_nil_iff]
  simp only [List.mem_singleton, exists_eq_left]
  change Resolved.truthy (condition.eval _ []) = true ↔ _
  rw [value]

/-- Under the same original premises, the output is empty exactly when the count condition
is false. Proof sketch: use the same semantic certificate and the empty-results observer. -/
theorem count_hasNoRows :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition name])).hasNoRows = true ↔
      Resolved.truthy (condition.eval ((Resolved.EvalContext.bound parameters).withRuns
        [Resolved.SubqueryRun.count (Resolved.countMatching (Resolved.EvalContext.bound parameters) subCondition table)]) []) = false := by
  obtain ⟨output, value⟩ := count_semantics index connection parameters condition position table subCondition name present calm
  rw [output, Output.hasNoRows_possibleResults, (Resolved.Query.simple_isSimple _ _ _ _).results_eq_nil_iff]
  simp only [List.mem_singleton, forall_eq]
  change Resolved.truthy (condition.eval _ []) = false ↔ _
  rw [value]

/-- Under the same original premises, the count statement gives no SQL error.
Proof sketch: every output of the result-list constructor is error-free. -/
theorem count_no_error :
    (resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere condition)
      [Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition name])).isError = false := by
  rw [(count_semantics index connection parameters condition position table subCondition name present calm).1]
  exact Output.isError_ofResults _

end
#print axioms count_semantics
#print axioms count_hasRows
#print axioms count_hasNoRows
#print axioms count_no_error
end ProofBoundaries
