import Belay.Sqlite.Model.InSubqueryEqualityLink
import Belay.Sqlite.Model.SimpleSubqueryRowsOutput
import Belay.Sqlite.Model.ExistsSubqueryOutput

set_option doc.verso true

/-! The output of a statement of one table with subqueries (task 20261027): {lit}`SELECT p1, p2, … FROM t WHERE
condition` with one subquery, as {name}`Belay.Sqlite.Model.Resolved.Query.oneTable` with the width 0. The output is
the rows of {lit}`t` in scan order that the condition keeps, with the result expressions. Two such statements with
conditions that keep the same rows give the same output. -/

namespace Belay.Sqlite.Model

/-- For every statement of {name}`Resolved.Query.oneTable` with one subquery, the statement is calm
({name}`Resolved.Statement.Calm`) when its condition, its result expressions and the expressions of the subquery are
calm ({name}`Resolved.Expr.Calm`). Proof sketch: the expressions of the statement are the condition, the result
expressions and the expressions of the subquery. -/
theorem Resolved.Query.oneTable_calm (position : Nat) (condition : Option Resolved.Expr)
    (projections : List Resolved.Expr) (names : List String) (inner : Resolved.Query)
    (conditionCalm : ∀ expression ∈ condition.toList, expression.Calm)
    (projectionsCalm : ∀ expression ∈ projections, expression.Calm)
    (innerCalm : ∀ expression ∈ inner.expressions, expression.Calm) :
    (Resolved.Statement.query (Resolved.Query.oneTable position 0 condition projections names) [inner]).Calm := by
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.oneTable_expressions, List.mem_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil] at member
  rcases member with (member | member) | member
  · exact conditionCalm expression member
  · exact projectionsCalm expression member
  · exact innerCalm expression member

/-- For every connection, values, table at a position of the database, condition, result expressions and subquery, when
the expressions of the statement are calm and have no fault over the empty row and over each row of the table in the
context of the statement, the output of the step of {name}`Resolved.Query.oneTable` with the subquery, with any clock and
index, is the rows that the condition keeps, in scan order, with the values of the result expressions, in normal form.
The condition and the result expressions are evaluated in the context of the statement. Proof sketch:
{name}`resolvedStepOutput_simple_rows_of_faultless` with the source rows of the table
({name}`Resolved.Query.source_first`) and the one result of {name}`Resolved.Query.Simple.results_eq`. -/
theorem resolvedStepOutput_oneTable_rows (clock : Option Clock) (index position : Nat) (connection : Connection)
    (parameters : List Value) (table : Table) (condition : Option Resolved.Expr) (projections : List Resolved.Expr)
    (names : List String) (inner : Resolved.Query)
    (present : connection.state.database.table position = some table)
    (conditionCalm : ∀ expression ∈ condition.toList, expression.Calm)
    (projectionsCalm : ∀ expression ∈ projections, expression.Calm)
    (innerCalm : ∀ expression ∈ inner.expressions, expression.Calm)
    (faultless : ∀ row ∈ [] :: Resolved.sourceRows table, ∀ expression ∈ condition.toList ++ projections,
      (expression.evaluate (connection.queryContext parameters
        (Resolved.Query.oneTable position 0 condition projections names) [inner]) row).2 = .none) :
    resolvedStepOutput clock index connection parameters
        (.query (Resolved.Query.oneTable position 0 condition projections names) [inner]) =
      .rows (Resolved.normalForm (((Resolved.sourceRows table).filter (Resolved.conditionKeeps condition
        (connection.queryContext parameters (Resolved.Query.oneTable position 0 condition projections names)
          [inner]))).map fun row => projections.map fun expression =>
        expression.eval (connection.queryContext parameters
          (Resolved.Query.oneTable position 0 condition projections names) [inner]) row)) := by
  have calm := Resolved.Query.oneTable_calm position condition projections names inner conditionCalm projectionsCalm
    innerCalm
  have simple := Resolved.Query.oneTable_simple position 0 condition projections names
  rw [resolvedStepOutput_simple_rows_of_faultless clock index connection parameters
    (Resolved.Query.oneTable position 0 condition projections names) [inner] simple
    { rows := Resolved.sourceRows table, width := table.shape.columns.length, fault := .none } calm
    (Resolved.Query.source_first _ _ _ position table rfl present) rfl ?_]
  · rw [simple.results_eq]
    simp [Resolved.filtered, Resolved.Query.oneTable, Resolved.Query.simple,
      Function.comp_def]
    rfl
  · intro row member expression inside
    rw [Resolved.Query.oneTable_expressions] at inside
    exact faultless row member expression inside

/-- **Same rows, same output.** For every connection, values, table at a position of the database, two optional
conditions, positions of result columns, and two subqueries, when the expressions of both statements are calm and have
no fault over the empty row and over each row of the table (each in the context of its own statement), and the two
conditions keep the same rows of the table (each in its own context), the steps of the two statements with any clock
and index give the same output. The result expressions are the cells of the table at the positions, which do not
depend on the context. Proof sketch: {name}`resolvedStepOutput_oneTable_rows` gives each output as the kept rows with
the cells; the lists of kept rows are equal by {name}`List.filter_congr`. -/
theorem resolvedStepOutput_oneTable_congr (clock : Option Clock) (index position : Nat) (connection : Connection)
    (parameters : List Value) (table : Table) (conditionFirst conditionSecond : Option Resolved.Expr)
    (columns : List Nat) (namesFirst namesSecond : List String) (innerFirst innerSecond : Resolved.Query)
    (present : connection.state.database.table position = some table)
    (calmFirst : ∀ expression ∈ conditionFirst.toList, expression.Calm)
    (calmSecond : ∀ expression ∈ conditionSecond.toList, expression.Calm)
    (innerCalmFirst : ∀ expression ∈ innerFirst.expressions, expression.Calm)
    (innerCalmSecond : ∀ expression ∈ innerSecond.expressions, expression.Calm)
    (faultlessFirst : ∀ row ∈ [] :: Resolved.sourceRows table, ∀ expression ∈ conditionFirst.toList,
      (expression.evaluate (connection.queryContext parameters
        (Resolved.Query.oneTable position 0 conditionFirst (columns.map .column) namesFirst) [innerFirst]) row).2 =
        .none)
    (faultlessSecond : ∀ row ∈ [] :: Resolved.sourceRows table, ∀ expression ∈ conditionSecond.toList,
      (expression.evaluate (connection.queryContext parameters
        (Resolved.Query.oneTable position 0 conditionSecond (columns.map .column) namesSecond) [innerSecond]) row).2 =
        .none)
    (sameKept : ∀ row ∈ Resolved.sourceRows table,
      Resolved.conditionKeeps conditionFirst (connection.queryContext parameters
        (Resolved.Query.oneTable position 0 conditionFirst (columns.map .column) namesFirst) [innerFirst]) row =
      Resolved.conditionKeeps conditionSecond (connection.queryContext parameters
        (Resolved.Query.oneTable position 0 conditionSecond (columns.map .column) namesSecond) [innerSecond]) row) :
    resolvedStepOutput clock index connection parameters
        (.query (Resolved.Query.oneTable position 0 conditionFirst (columns.map .column) namesFirst) [innerFirst]) =
      resolvedStepOutput clock index connection parameters
        (.query (Resolved.Query.oneTable position 0 conditionSecond (columns.map .column) namesSecond)
          [innerSecond]) := by
  have columnsCalm : ∀ expression ∈ columns.map Resolved.Expr.column, expression.Calm := by
    intro expression member
    obtain ⟨column, _, rfl⟩ := List.mem_map.mp member
    exact Resolved.Expr.calm_column _
  rw [resolvedStepOutput_oneTable_rows clock index position connection parameters table conditionFirst
      (columns.map .column) namesFirst innerFirst present calmFirst columnsCalm innerCalmFirst ?_,
    resolvedStepOutput_oneTable_rows clock index position connection parameters table conditionSecond
      (columns.map .column) namesSecond innerSecond present calmSecond columnsCalm innerCalmSecond ?_]
  · congr 3
    · funext row
      simp [Resolved.Expr.eval_column]
    · exact List.filter_congr sameKept
  · intro row member expression inside
    rcases List.mem_append.mp inside with inside | inside
    · exact faultlessSecond row member expression inside
    · obtain ⟨column, _, rfl⟩ := List.mem_map.mp inside
      rfl
  · intro row member expression inside
    rcases List.mem_append.mp inside with inside | inside
    · exact faultlessFirst row member expression inside
    · obtain ⟨column, _, rfl⟩ := List.mem_map.mp inside
      rfl

end Belay.Sqlite.Model
