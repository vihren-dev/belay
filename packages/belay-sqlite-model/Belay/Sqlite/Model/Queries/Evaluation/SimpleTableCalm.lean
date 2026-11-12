import Belay.Sqlite.Model.Queries.Evaluation.SimpleQueryAppend
import Belay.Sqlite.Model.Queries.Evaluation.ExprCalmLaws

set_option doc.verso true

/-! A read of one table is calm when its expressions are (ADR 0017, S6). A calm statement reads no clock
and no counter and calls no function that can fail, so its step gives the one output that the model gives
for its rows. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every table position, optional filter, result columns and names: if every expression of the
filter and every scalar result column is calm ({name}`Expr.Calm`), and no result column has an operand
other than its scalar (an aggregate column has operands), then the statement of the simple query of that
table, with no subquery, is calm. Plain words: a one-table read with calm parts is calm. Proof sketch:
the expressions of the statement are the filter, the scalar columns and the operands of the columns; the
source of a table has none. -/
theorem Statement.simpleTable_calm (position : Nat) (filter : Option Expr) (columns : List Output)
    (names : List String)
    (calm : ∀ expression ∈ filter.toList ++ columns.flatMap Output.scalars, expression.Calm)
    (scalar : ∀ column ∈ columns, column.operands = []) :
    (Statement.query (Query.simple [QuerySource.first position] filter columns names) []).Calm := by
  intro expression member
  simp only [Statement.clockExpressions, Query.expressions, Query.keptExpressions,
    Query.simple, QuerySource.first, QuerySource.expressions, List.mem_append, List.mem_flatMap,
    List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false, List.map_nil] at member
  apply calm
  simp only [List.mem_append, List.mem_flatMap]
  rcases member with (member | ⟨source, rfl, member⟩) | (member | member) | member
  · exact Or.inl member
  · simp at member
  · obtain ⟨column, columnMember, member⟩ := member
    exact Or.inr ⟨column, columnMember, member⟩
  · obtain ⟨column, columnMember, member⟩ := member
    rw [scalar column columnMember] at member
    simp at member
  · simp at member

/-- For every table position, optional filter, column position and names: if every expression of the
filter is calm, the statement of the simple query that reads the one column at that position of the table,
with no subquery, is calm. Plain words: a one-column read of one table with a calm {lit}`WHERE` is calm.
Proof sketch: {name}`Statement.simpleTable_calm`; a column is calm ({name}`Expr.calm_column`) and has no
other operand. -/
theorem Statement.simpleColumn_calm (position : Nat) (filter : Option Expr) (index : Nat) (names : List String)
    (calm : ∀ expression ∈ filter.toList, expression.Calm) :
    (Statement.query (Query.simple [QuerySource.first position] filter [.scalar (.column index)] names) []).Calm := by
  apply Statement.simpleTable_calm
  · intro expression member
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Output.scalars, List.mem_append,
      List.mem_singleton] at member
    rcases member with member | rfl
    · exact calm expression member
    · exact Expr.calm_column index
  · intro column member
    cases List.mem_singleton.mp member
    rfl

/-- For every aggregate-free result column list whose columns read only columns below a width, no column
has an operand other than its scalar. Proof sketch: a column that reads below a width is scalar, and a
scalar has no operands. -/
theorem Output.operands_of_readsBelow {width : Nat} {column : Output} (below : column.readsBelow width = true) :
    column.operands = [] := by
  cases column with
  | scalar term => rfl
  | aggregate function => simp [Output.readsBelow] at below

end Belay.Sqlite.Model.Resolved
