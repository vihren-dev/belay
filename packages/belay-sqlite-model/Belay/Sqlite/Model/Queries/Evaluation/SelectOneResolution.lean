import Belay.Sqlite.Model.Queries.Select.SimpleStatementResolution
import Belay.Sqlite.Model.Queries.Evaluation.StatementQuiet

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every condition whose expressions are calm ({name}`Resolved.Expr.Calm`) and every position, the
statement of the query {lit}`SELECT 1 FROM t WHERE p` that resolution gives is calm
({name}`Resolved.Statement.Calm`): the literal one is calm, and the first source of a table has no
expression. Proof sketch: the expressions of the statement are the condition and the literal. -/
theorem Resolved.Statement.Calm.selectOne (position : Nat) (condition : Option Resolved.Expr)
    (calm : ∀ expression ∈ condition.toList, expression.Calm) :
    (Resolved.Statement.query (Resolved.Query.simple [Resolved.QuerySource.first position] condition
      [.scalar (.literal (.integer 1))] ["1"]) []).Calm := by
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.expressions, Resolved.Query.keptExpressions,
    Resolved.Query.simple, Resolved.QuerySource.first, Resolved.QuerySource.expressions, List.mem_append,
    List.mem_flatMap, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false] at member
  have literal : (Resolved.Expr.literal (.integer 1)).Calm := by
    simp [Resolved.Expr.Calm, Resolved.Expr.any, Resolved.Expr.isFallibleCall, Resolved.Expr.readsClockHere,
      Resolved.Expr.readsCounterHere]
  simp only [Resolved.Output.scalars, Resolved.Output.operands, List.mem_singleton, List.not_mem_nil, exists_eq_left,
    List.map_nil, or_false, Option.toList_none] at member
  rcases member with member | rfl
  · exact calm expression member
  · exact literal

/-- For every condition whose expressions are quiet ({name}`Resolved.Expr.Quiet`) and every position, the
statement of the query {lit}`SELECT 1 FROM t WHERE p` that resolution gives is quiet
({name}`Resolved.Statement.Quiet`): the literal one is quiet, and the first source of a table has no
expression. Proof sketch: as for {name}`Resolved.Statement.Calm.selectOne`; the expressions of the statement
are the condition and the literal. -/
theorem Resolved.Statement.Quiet.selectOne (position : Nat) (condition : Option Resolved.Expr)
    (quiet : ∀ expression ∈ condition.toList, expression.Quiet) :
    (Resolved.Statement.query (Resolved.Query.simple [Resolved.QuerySource.first position] condition
      [.scalar (.literal (.integer 1))] ["1"]) []).Quiet := by
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.expressions, Resolved.Query.keptExpressions,
    Resolved.Query.simple, Resolved.QuerySource.first, Resolved.QuerySource.expressions, List.mem_append,
    List.mem_flatMap, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false] at member
  have literal : (Resolved.Expr.literal (.integer 1)).Quiet := by
    simp [Resolved.Expr.Quiet, Resolved.Expr.any, Resolved.Expr.readsClockHere, Resolved.Expr.readsCounterHere]
  simp only [Resolved.Output.scalars, Resolved.Output.operands, List.mem_singleton, List.not_mem_nil, exists_eq_left,
    List.map_nil, or_false, Option.toList_none] at member
  rcases member with member | rfl
  · exact quiet expression member
  · exact literal

end Belay.Sqlite.Model
