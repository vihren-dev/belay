import Belay.Sqlite.Model.Queries.Evaluation.StatementCalm

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolved

/-- A quiet expression: none of its parts is a read of the clock ({name}`Expr.readsClockHere`) or a
call of a counter function ({name}`Expr.readsCounterHere`). A call of {lit}`abs` is quiet and not calm
({name}`Expr.Calm`), because {lit}`abs` can fail. -/
def Expr.Quiet (expression : Expr) : Prop :=
  expression.any Expr.readsClockHere = false ∧ ∀ kind, expression.any (Expr.readsCounterHere kind) = false

/-- A quiet statement: every expression that its evaluation reads is quiet ({name}`Expr.Quiet`,
{name}`Statement.clockExpressions`). A statement without expressions is quiet. -/
def Statement.Quiet (statement : Statement) : Prop :=
  ∀ expression ∈ statement.clockExpressions, expression.Quiet

/-- Every calm expression is quiet. Proof sketch: calm is the three conditions, and quiet is the last two. -/
theorem Expr.Calm.quiet {expression : Expr} (calm : expression.Calm) : expression.Quiet := ⟨calm.2.1, calm.2.2⟩

/-- Every calm statement is quiet. Proof sketch: {name}`Expr.Calm.quiet` for each expression. -/
theorem Statement.Calm.quiet {statement : Statement} (calm : statement.Calm) : statement.Quiet :=
  fun expression member => (calm expression member).quiet

end Belay.Sqlite.Model.Resolved
