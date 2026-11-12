import Belay.Sqlite.Model.Queries.Evaluation.StatementQuiet
import Belay.Sqlite.Model.Queries.Preparation.TableInfoResolution

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- For every pragma rows and condition that is calm, the statement of the simple query of the pragma source with that
condition and the literal one is calm ({name}`Resolved.Statement.Calm`). Proof sketch: the expressions of the statement are
the condition and the literal, and a pragma source has no expression. -/
theorem Statement.Calm.selectOne_pragma (pragma : Resolved.PragmaRows) (condition : Option Resolved.Expr)
    (calm : ∀ expression ∈ condition.toList, expression.Calm) :
    (Resolved.Statement.query (Resolved.Query.simple [Resolved.QuerySource.pragma pragma] condition
      [.scalar (.literal (.integer 1))] ["1"]) []).Calm := by
  intro expression member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.expressions, Resolved.Query.keptExpressions,
    Resolved.Query.simple, Resolved.QuerySource.pragma, Resolved.QuerySource.expressions, List.mem_append,
    List.mem_flatMap, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false] at member
  have literal : (Resolved.Expr.literal (.integer 1)).Calm := by
    simp [Resolved.Expr.Calm, Resolved.Expr.any, Resolved.Expr.isFallibleCall, Resolved.Expr.readsClockHere,
      Resolved.Expr.readsCounterHere]
  simp only [Resolved.Output.scalars, Resolved.Output.operands, List.mem_singleton, List.not_mem_nil, exists_eq_left,
    List.map_nil, or_false, Option.toList_none] at member
  rcases member with member | rfl
  · exact calm expression member
  · exact literal

/-- For every optional condition {lit}`c`, expression {lit}`e` and output names: when each part of
{lit}`c` and {lit}`e` are quiet ({name}`Expr.Quiet`), the statement {lit}`SELECT e WHERE c` without
{lit}`FROM` is quiet. Proof sketch: the expressions of the statement are {lit}`c` and {lit}`e`. -/
theorem Statement.Quiet.selectNoFrom (condition : Option Expr) (expression : Expr) (names : List String)
    (conditionQuiet : ∀ part ∈ condition.toList, part.Quiet) (quiet : expression.Quiet) :
    (Statement.query (Query.simple [] condition [.scalar expression] names) []).Quiet := by
  intro part member
  simp only [Resolved.Statement.clockExpressions, Resolved.Query.expressions, Resolved.Query.keptExpressions,
    Resolved.Query.simple, List.mem_append, List.flatMap_nil, Resolved.Output.scalars, Resolved.Output.operands,
    List.mem_singleton, List.map_nil, List.append_nil, List.flatMap_cons, Option.toList_none] at member
  rcases member with member | member
  · exact conditionQuiet part member
  · rw [member]
    exact quiet

end Belay.Sqlite.Model.Resolved
