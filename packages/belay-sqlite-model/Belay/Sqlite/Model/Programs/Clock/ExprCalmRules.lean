import Belay.Sqlite.Model.Queries.Evaluation.ExprCalmLaws

set_option doc.verso true

/-! The calm rules of the resolved expressions that {lit}`ExprCalmLaws.lean` does not cover
(ADR 0027 D1, expression phase). An expression is calm ({name}`Belay.Sqlite.Model.Resolved.Expr.Calm`)
when no part of it is a fallible call, a clock read or a counter call; the execution rule reads
a calm statement with a context of its values alone. Arithmetic, {lit}`CAST`, {lit}`COALESCE` and
{lit}`IN` of a list are calm when their parts are; a call of a function that cannot fail is calm
when its arguments are ({lit}`Arguments.Calm`); a time keyword, a
counter call and a JSON call are never calm. -/

namespace Belay.Sqlite.Model.Resolved

/-- A time keyword is not calm: it reads the clock. Proof sketch: the keyword is a clock read
({lit}`Expr.readsClockHere`). -/
theorem Expr.not_calm_now (keyword : TimeKeyword) : ¬ (Expr.now keyword).Calm := by
  simp [Expr.Calm, Expr.any, Expr.readsClockHere]

end Belay.Sqlite.Model.Resolved
