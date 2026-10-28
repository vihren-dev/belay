import Belay.Sqlite.Model.SelectOneOutput
import Belay.Sqlite.Model.DuplicateKeyQuery
import Belay.Sqlite.Model.NotExistsSubqueryOutput

set_option doc.verso true

/-! The output of {lit}`SELECT 1 WHERE NOT EXISTS (SELECT c FROM t [WHERE w] GROUP BY k HAVING count(*) > 1)` (ADR 0017, S4 and S6):
a statement without {lit}`FROM` and with one subquery, the duplicate-key query of one table
({name}`Belay.Sqlite.Model.Resolved.Query.duplicateKeys`). The subquery gives a row for each group of more than one
row, so the statement has rows exactly when every group of the rows that {lit}`WHERE` keeps has one row at most. -/

namespace Belay.Sqlite.Model

/-- The expressions of the duplicate-key query of the first source of a table are its {lit}`WHERE` condition if it has one,
the result column, the grouping key, and the condition {lit}`count(*) > 1`. Proof sketch: the definitions compute. -/
theorem Resolved.Query.duplicateKeys_first_expressions (position : Nat) (filter : Option Resolved.Expr) (column : Resolved.Expr) (name : String) (key : Resolved.Expr)
    (collation : Collation) :
    (Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation).expressions =
      filter.toList ++ [column, key,
        .compare .gt none (.aggregateValue 0) (.literal (.integer 1)) .binary] := by
  simp [Resolved.Query.expressions, Resolved.Query.keptExpressions, Resolved.Query.duplicateKeys,
    Resolved.QuerySource.first, Resolved.QuerySource.expressions, Resolved.Output.scalars, Resolved.Output.operands]

/-- The condition {lit}`count(*) > 1` is calm: it has no fallible call, no clock read and no counter read. Proof
sketch: it is a comparison of an aggregate value and a literal. -/
theorem Resolved.Expr.calm_moreThanOne :
    (Resolved.Expr.compare .gt none (.aggregateValue 0) (.literal (.integer 1)) .binary).Calm := by
  simp [Resolved.Expr.Calm, Resolved.Expr.any, Resolved.Expr.isFallibleCall, Resolved.Expr.readsClockHere,
    Resolved.Expr.readsCounterHere]

/-- For every calm condition {lit}`c`, calm {lit}`WHERE` condition, result column and key, the statement of
{lit}`SELECT 1 WHERE c` with the duplicate-key query of the first source of a table as its one subquery is calm
({name}`Resolved.Statement.Calm`). Proof sketch: the expressions of the statement are the condition, the literal one,
and the expressions of the subquery
({name}`Resolved.Query.duplicateKeys_first_expressions`). -/
theorem Resolved.Statement.Calm.selectOne_duplicateKeys (position : Nat) (main : Resolved.Expr)
    (filter : Option Resolved.Expr) (column : Resolved.Expr) (name : String) (key : Resolved.Expr)
    (collation : Collation) (mainCalm : main.Calm) (filterCalm : ∀ condition, filter = some condition → condition.Calm)
    (columnCalm : column.Calm) (keyCalm : key.Calm) :
    (Resolved.Statement.query (Resolved.Query.selectOneWhere main)
      [Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation]).Calm := by
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.selectOneWhere_expressions,
    Resolved.Query.duplicateKeys_first_expressions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (rfl | rfl) | filterMember | rfl | rfl | rfl
  · exact mainCalm
  · exact Resolved.Expr.calm_literal _
  · exact filterCalm expression (Option.mem_toList.1 filterMember)
  · exact columnCalm
  · exact keyCalm
  · exact Resolved.Expr.calm_moreThanOne

/-- For every connection, values, query and calm statement of the query with one subquery that is the duplicate-key
query of the table at a position of the database, subquery 0 of the context for the outer row with no cells has the
result rows of the duplicate-key query over the rows of the table in scan order as its rows, no fault and certain rows.
Proof sketch: {name}`Connection.queryContext_subquery_zero` and {name}`Resolved.Query.duplicateKeys_subqueryRun` with the
source rows of {name}`Resolved.Query.source_first`; the context is quiet, so no expression has a fault. -/
theorem Connection.queryContext_duplicateKeys_zero (connection : Connection) (parameters : List Value)
    (query : Resolved.Query) (position : Nat) (table : Table) (filter : Option Resolved.Expr) (column : Resolved.Expr) (name : String) (key : Resolved.Expr)
    (collation : Collation)
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query query
      [Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation]).Calm) :
    (connection.queryContext parameters query
      [Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation]).subqueries 0 [] =
      { rows := (Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation).results
          (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table),
        fault := .none,
        firstCertain := (Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation).windowCertain
          (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) (some 1),
        rowsCertain := true, ending := .done } := by
  have plain := calm.subquery_plain (List.mem_singleton_self _)
  rw [connection.queryContext_subquery_zero parameters query _ calm]
  refine Resolved.Query.duplicateKeys_subqueryRun _ _ _ _ _ _ _ _ _
    (Resolved.Query.source_first _ _ _ position table rfl present) rfl plain fun row _ expression member => ?_
  simp only [List.all_eq_true, Bool.not_eq_true'] at plain
  exact Resolved.Expr.fault_of_plain _ (Resolved.EvalContext.bound_quiet parameters) row expression (plain expression member)

/-- For every calm SELECT 1 statement with a duplicate-key subquery over an existing table,
the complete output contains integer one when every group of kept rows has at most one row,
and is empty otherwise. Groups use the supplied key and collation; the filter runs before grouping.
Proof sketch: substitute the grouped subquery result and characterize its empty list. -/
theorem resolvedStepOutput_notExists_duplicateKeys (index position : Nat) (connection : Connection)
    (parameters : List Value) (table : Table) (filter : Option Resolved.Expr) (column : Resolved.Expr) (name : String) (key : Resolved.Expr)
    (collation : Collation)
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query (Resolved.Query.selectOneWhere (.not (.exists 0)))
      [Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation]).Calm) :
    resolvedStepOutput none index connection parameters (.query (Resolved.Query.selectOneWhere (.not (.exists 0)))
      [Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation]) =
      .rows (if (Resolved.groups (Resolved.EvalContext.bound parameters) [(key, collation)]
        (Resolved.keptRows (Resolved.EvalContext.bound parameters) filter (Resolved.sourceRows table))).all
          (fun group => decide (group.length ≤ 1)) then [[.integer 1]] else []) := by
  have run := connection.queryContext_duplicateKeys_zero parameters _ position table filter column name key collation present calm
  rw [resolvedStepOutput_selectOne index connection parameters _ _ calm
    (by rw [Resolved.Expr.fault_not, Resolved.Expr.fault_exists, run])]
  simp only [Resolved.Expr.eval_not, Resolved.Expr.eval_exists, Resolved.truthy_not, run,
    Resolved.falsy, truthy_truth, isNull_truth, Bool.not_false, Bool.true_and, Bool.not_not]
  have same : ((Resolved.Query.duplicateKeys [Resolved.QuerySource.first position] filter column name key collation).results
      (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table)).isEmpty =
      (Resolved.groups (Resolved.EvalContext.bound parameters) [(key, collation)]
        (Resolved.keptRows (Resolved.EvalContext.bound parameters) filter (Resolved.sourceRows table))).all
          (fun group => decide (group.length ≤ 1)) := by
    apply Bool.eq_iff_iff.mpr
    simp [List.isEmpty_iff, Resolved.Query.duplicateKeys_results, List.filter_eq_nil_iff, Nat.not_lt]
  rw [same]

end Belay.Sqlite.Model
