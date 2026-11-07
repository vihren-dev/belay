import Belay.Sqlite.Model.NoFromQuerySteps
import Belay.Sqlite.Model.SimpleSubqueryRun
import Belay.Sqlite.Model.TableSourceLaws
import Belay.Sqlite.Model.ExprEvalLaws
import Belay.Sqlite.Model.ExprCalmLaws
import Belay.Sqlite.Model.CountOf

set_option doc.verso true

/-! The context of a statement with one subquery (ADR 0017, S4): for a calm statement, subquery 0
of its context is the run of the subquery in the context of the values. The statement
{lit}`SELECT 1 WHERE c` with the one subquery {lit}`SELECT e FROM t WHERE p` is calm when {lit}`c`,
{lit}`p` and {lit}`e` are calm, and quiet when they are quiet; with the count query {lit}`SELECT count(*) FROM t WHERE p` as its subquery, it is
calm when both conditions are calm. -/

namespace Belay.Sqlite.Model

/-- The context of the subquery evaluation of a calm statement is quiet: the values bound to the
parameters, with no subquery and no counter. Proof sketch: the context gives no fault and certain
rows for every index. -/
theorem Resolved.EvalContext.bound_quiet (parameters : List Value) : (Resolved.EvalContext.bound parameters).Quiet :=
  fun _ _ => ⟨rfl, rfl, rfl⟩

/-- For every connection, values, query and calm statement of the query with one subquery, subquery 0 of the context
of the statement on the connection, for an outer row, is the run of that subquery
({name}`Resolved.Query.subqueryRun`) in the context of the values, over the database of the connection. Proof
sketch: the statement reads no counter, so its context is the context of the values with the
subquery list at depth one, and the definition of {name}`Resolved.subqueryContext` computes. -/
theorem Connection.queryContext_subquery_zero (connection : Connection) (parameters : List Value)
    (query inner : Resolved.Query) (calm : (Resolved.Statement.query query [inner]).Calm) (outer : List Value) :
    (connection.queryContext parameters query [inner]).subqueries 0 outer =
      inner.subqueryRun (Resolved.EvalContext.bound parameters) connection.state.database outer := by
  simp only [Connection.queryContext, calm.counterReads, Resolved.statementContext]
  rfl

/-- For every position, condition, column expression and names, the expressions of the simple query of the first
source of a table with that one result column are its condition, if any, and the expression of the column. Proof
sketch: the definitions compute. -/
theorem Resolved.Query.simple_first_expressions (position : Nat) (condition : Option Resolved.Expr)
    (value : Resolved.Expr) (names : List String) :
    (Resolved.Query.simple [Resolved.QuerySource.first position] condition [.scalar value] names).expressions =
      condition.toList ++ [value] := by
  simp [Resolved.Query.expressions, Resolved.Query.keptExpressions, Resolved.Query.simple, Resolved.QuerySource.first,
    Resolved.QuerySource.expressions, Resolved.Output.scalars, Resolved.Output.operands]

/-- For every calm condition {lit}`c`, every calm condition {lit}`p` of the subquery and every calm column
expression {lit}`e`, the statement {lit}`SELECT 1 WHERE c` with the one subquery {lit}`SELECT e FROM t WHERE p`
that resolution gives is calm ({name}`Resolved.Statement.Calm`). For {lit}`EXISTS`, {lit}`e` is the literal one.
Proof sketch: the expressions of the statement are {lit}`c`, the literal one of the statement's query, {lit}`p`
and {lit}`e` ({name}`Resolved.Query.simple_first_expressions`); the first source of a table has no expression. -/
theorem Resolved.Statement.Calm.selectOne_subquery (position : Nat) (main : Resolved.Expr)
    (subCondition : Option Resolved.Expr) (value : Resolved.Expr) (names : List String) (mainCalm : main.Calm)
    (subCalm : ∀ expression ∈ subCondition.toList, expression.Calm) (valueCalm : value.Calm) :
    (Resolved.Statement.query (Resolved.Query.selectOneWhere main)
      [Resolved.Query.simple [Resolved.QuerySource.first position] subCondition [.scalar value] names]).Calm := by
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.selectOneWhere_expressions,
    Resolved.Query.simple_first_expressions, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl) | member | rfl
  · exact mainCalm
  · exact Resolved.Expr.calm_literal _
  · exact subCalm expression member
  · exact valueCalm

/-- For every quiet condition {lit}`c`, every quiet condition {lit}`p` of the subquery and every quiet column
expression {lit}`e`, the statement {lit}`SELECT 1 WHERE c` with the one subquery {lit}`SELECT e FROM t WHERE p`
that resolution gives is quiet ({name}`Resolved.Statement.Quiet`). Proof sketch: as for
{name}`Resolved.Statement.Calm.selectOne_subquery`. -/
theorem Resolved.Statement.Quiet.selectOne_subquery (position : Nat) (main : Resolved.Expr)
    (subCondition : Option Resolved.Expr) (value : Resolved.Expr) (names : List String) (mainQuiet : main.Quiet)
    (subQuiet : ∀ expression ∈ subCondition.toList, expression.Quiet) (valueQuiet : value.Quiet) :
    (Resolved.Statement.query (Resolved.Query.selectOneWhere main)
      [Resolved.Query.simple [Resolved.QuerySource.first position] subCondition [.scalar value] names]).Quiet := by
  have literal : (Resolved.Expr.literal (.integer 1)).Quiet := by
    simp [Resolved.Expr.Quiet, Resolved.Expr.any, Resolved.Expr.readsClockHere, Resolved.Expr.readsCounterHere]
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.selectOneWhere_expressions,
    Resolved.Query.simple_first_expressions, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl) | member | rfl
  · exact mainQuiet
  · exact literal
  · exact subQuiet expression member
  · exact valueQuiet

/-- For every calm condition {lit}`c` and every calm condition of the subquery, the statement
{lit}`SELECT 1 WHERE c` with the count query of the first source of a table as its one subquery is calm
({name}`Resolved.Statement.Calm`). Proof sketch: the expressions of the statement are the condition, the
literal one, and the condition of the subquery ({name}`Resolved.Query.countOf_expressions`); the first
source has no expression. -/
theorem Resolved.Statement.Calm.selectOne_count (position : Nat) (main : Resolved.Expr) (subCondition : Option Resolved.Expr)
    (name : String) (mainCalm : main.Calm) (subCalm : ∀ expression ∈ subCondition.toList, expression.Calm) :
    (Resolved.Statement.query (Resolved.Query.selectOneWhere main)
      [Resolved.Query.countOf [Resolved.QuerySource.first position] subCondition name]).Calm := by
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.selectOneWhere_expressions,
    Resolved.Query.countOf_expressions, Resolved.QuerySource.first, Resolved.QuerySource.expressions,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, Option.toList_none, false_or, or_false] at member
  rcases member with (rfl | rfl) | member
  · exact mainCalm
  · exact Resolved.Expr.calm_literal _
  · exact subCalm expression member

end Belay.Sqlite.Model
