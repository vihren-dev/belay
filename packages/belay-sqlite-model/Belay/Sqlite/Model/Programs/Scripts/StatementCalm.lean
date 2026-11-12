import Belay.Sqlite.Model.Schema.Dispatch.StatementCounterReads
import Belay.Sqlite.Model.Programs.Clock.StatementClock
import Belay.Sqlite.Model.Queries.Evaluation.StatementCalm

set_option doc.verso true

/-! Calm expressions and statements (ADR 0017, S4): an expression that has no fallible call, reads
no clock and calls no counter function. These syntactic conditions let query-output laws
discharge the corresponding runtime checks without assumptions about a clock or counter values. -/

namespace Belay.Sqlite.Model.Resolved

/-- For every calm statement, the statement reads no clock ({name}`Statement.readsClock`). Proof
sketch: a clock read is a part of an expression that reads the clock, which the calm expression
lacks. -/
theorem Statement.Calm.readsClock {statement : Statement} (calm : statement.Calm) : statement.readsClock = false := by
  unfold Statement.readsClock Expr.readsClock
  simp only [List.any_eq_false]
  exact fun expression member => by simp [(calm expression member).2.1]

/-- For every calm statement, the statement reads no counter ({name}`Statement.counterReads` is
empty). Proof sketch: a counter that the statement reads is a part of one of its expressions that
calls the counter function, which a calm expression lacks. -/
theorem Statement.Calm.counterReads {statement : Statement} (calm : statement.Calm) : statement.counterReads = [] := by
  unfold Statement.counterReads
  simp only [List.filter_eq_nil_iff, List.any_eq_true, not_exists, not_and, Bool.not_eq_true]
  intro kind _ expression member
  simp [(calm expression member).2.2 kind]

/-- For every calm statement and every counters, no counter that the statement reads is unknown
({name}`Counters.firstUnknown`), because it reads none ({name}`Statement.Calm.counterReads`). -/
theorem Statement.Calm.firstUnknown {statement : Statement} (calm : statement.Calm) (counters : Counters) :
    counters.firstUnknown statement.counterReads = none := by
  rw [calm.counterReads]
  rfl

end Belay.Sqlite.Model.Resolved
