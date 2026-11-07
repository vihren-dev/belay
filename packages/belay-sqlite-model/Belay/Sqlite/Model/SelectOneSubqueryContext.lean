import Belay.Sqlite.Model.SelectOneOutput
import Belay.Sqlite.Model.SimpleSubqueryRun
import Belay.Sqlite.Model.TableSourceLaws
import Belay.Sqlite.Model.ExprEvalLaws
import Belay.Sqlite.Model.ExprCalmLaws

set_option doc.verso true

/-! The context of a statement with one subquery (ADR 0017, S4): for a calm statement, subquery 0
of its context is the run of the subquery in the context of the values, and for the simple query of a
table that run has the result rows of the query over the table. The statement {lit}`SELECT 1 WHERE c`
with the one subquery {lit}`SELECT 1 FROM t WHERE p` is calm when both conditions are calm, and quiet
when both are quiet. -/

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

/-- For every connection, values, query and calm statement of the query with one subquery that is the
simple query of the table at a position of the database, subquery 0 of the context for the outer row with no cells has the
one result of the simple query over the rows of the table in scan order (rowid order, or primary-key order for a {lit}`WITHOUT ROWID` table) as its rows, no fault and certain rows. Proof sketch:
{name}`Connection.queryContext_subquery_zero` and {name}`Resolved.Query.subqueryRun_simple` with the source rows of
{name}`Resolved.Query.source_first`; the context is quiet, so no expression has a fault. -/
theorem Connection.queryContext_tableSubquery_zero (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (position : Nat) (table : Table) (condition : Option Resolved.Expr)
    (columns : List Resolved.Output) (names : List String)
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query query [Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names]).Calm) :
    (connection.queryContext parameters query [Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names]).subqueries 0 [] =
      { rows := (Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names).results
          (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table),
        fault := .none,
        firstCertain := (Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names).windowCertain
          (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) (some 1),
        rowsCertain := true, ending := .done } := by
  have plain := calm.subquery_plain (List.mem_singleton_self _)
  rw [connection.queryContext_subquery_zero parameters query _ calm]
  refine Resolved.Query.subqueryRun_simple _ _ _ (Resolved.Query.simple_isSimple _ _ _ _) rfl _
    (Resolved.Query.source_first _ _ _ position table rfl present) rfl plain fun row _ expression member => ?_
  simp only [List.all_eq_true, Bool.not_eq_true'] at plain
  exact Resolved.Expr.fault_of_plain _ (Resolved.EvalContext.bound_quiet parameters) row expression (plain expression member)

/-- The expressions of the simple query of the first source of a table are its condition, if any, and
the expressions of its result column {lit}`1`. Proof sketch: the definitions compute. -/
theorem Resolved.Query.simple_first_expressions (position : Nat) (condition : Option Resolved.Expr) :
    (Resolved.Query.simple [Resolved.QuerySource.first position] condition [.scalar (.literal (.integer 1))] ["1"]).expressions =
      condition.toList ++ [.literal (.integer 1)] := by
  simp [Resolved.Query.expressions, Resolved.Query.keptExpressions, Resolved.Query.simple, Resolved.QuerySource.first,
    Resolved.QuerySource.expressions, Resolved.Output.scalars, Resolved.Output.operands]

/-- For every calm condition {lit}`c` and every calm condition of the subquery, the statement of
{lit}`SELECT 1 WHERE c` with the one subquery {lit}`SELECT 1 FROM t WHERE p` that resolution gives is calm
({name}`Resolved.Statement.Calm`): the literal one is calm, and the first source of a table has no
expression. Proof sketch: the expressions of the statement are the condition, the literal one of the
statement's query, the subquery's condition and the literal one of the subquery. -/
theorem Resolved.Statement.Calm.selectOne_subquery (position : Nat) (main : Resolved.Expr)
    (subCondition : Option Resolved.Expr) (mainCalm : main.Calm)
    (subCalm : ∀ expression ∈ subCondition.toList, expression.Calm) :
    (Resolved.Statement.query (Resolved.Query.selectOneWhere main)
      [Resolved.Query.simple [Resolved.QuerySource.first position] subCondition
        [.scalar (.literal (.integer 1))] ["1"]]).Calm := by
  have literal : (Resolved.Expr.literal (.integer 1)).Calm := Resolved.Expr.calm_literal _
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.selectOneWhere_expressions,
    Resolved.Query.simple_first_expressions, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl) | member | rfl
  · exact mainCalm
  · exact literal
  · exact subCalm expression (by simpa using member)
  · exact literal

/-- For every quiet condition {lit}`c` and every quiet condition of the subquery, the statement of
{lit}`SELECT 1 WHERE c` with the one subquery {lit}`SELECT 1 FROM t WHERE p` that resolution gives is quiet
({name}`Resolved.Statement.Quiet`). Proof sketch: as for {name}`Resolved.Statement.Calm.selectOne_subquery`. -/
theorem Resolved.Statement.Quiet.selectOne_subquery (position : Nat) (main : Resolved.Expr)
    (subCondition : Option Resolved.Expr) (mainQuiet : main.Quiet)
    (subQuiet : ∀ expression ∈ subCondition.toList, expression.Quiet) :
    (Resolved.Statement.query (Resolved.Query.selectOneWhere main)
      [Resolved.Query.simple [Resolved.QuerySource.first position] subCondition
        [.scalar (.literal (.integer 1))] ["1"]]).Quiet := by
  have literal : (Resolved.Expr.literal (.integer 1)).Quiet := by
    simp [Resolved.Expr.Quiet, Resolved.Expr.any, Resolved.Expr.readsClockHere, Resolved.Expr.readsCounterHere]
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.selectOneWhere_expressions,
    Resolved.Query.simple_first_expressions, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl) | member | rfl
  · exact mainQuiet
  · exact literal
  · exact subQuiet expression (by simpa using member)
  · exact literal

end Belay.Sqlite.Model
