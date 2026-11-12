import Belay.Sqlite.Model.Queries.Evaluation.ExprEvalLaws

set_option doc.verso true

/-! The value rules of the resolved expressions that {lit}`ExprEvalLaws.lean` does not cover
(ADR 0027 D1, expression phase): arithmetic, {lit}`CAST`, {lit}`COALESCE`, the JSON, date and
time and scalar function calls, {lit}`iif`, a time keyword, a counter call, {lit}`IN` of a list
and an aggregate value, and the truth of {lit}`IS NULL`. With those laws every one of the 21
constructors has a value rule. Each rule holds in every context and on every row; the fault of
the expression is a separate obligation ({lit}`ExprFaultRules.lean`). -/

namespace Belay.Sqlite.Model.Resolved

/-- The value of a time keyword is its text at the context's clock ({name}`TimeKeyword.value`).
Proof sketch: the definition computes. -/
theorem Expr.eval_now (context : EvalContext) (row : List Value) (keyword : TimeKeyword) :
    (Expr.now keyword).eval context row = keyword.value context.clock := rfl

/-- The value of a counter call is the context's counter of the kind as an integer, or NULL when
the counter is unknown. Proof sketch: the definition computes. -/
theorem Expr.eval_counter (context : EvalContext) (row : List Value) (kind : CounterKind) :
    (Expr.counter kind).eval context row = ((context.counters.read kind).map Value.integer).getD .null := rfl

end Belay.Sqlite.Model.Resolved
