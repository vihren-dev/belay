import Belay.Sqlite.Model.ScriptRunPositions

set_option doc.verso true

/-! The run of {lit}`ScriptRun.lean` does not depend on the index at which it starts, when the
run has no clock or a clock that gives the same value at every index. The index reaches a
statement's step only through its clock value and the position of a failure
({name}`Belay.Sqlite.Model.Outcome.failure`), and a failure position reaches neither the output
nor the connection after the statement. The surface's runs have no clock, so a script that
follows another one runs as from index 0. -/

namespace Belay.Sqlite.Model

/-- For every state, position, effect and next state: if the effect's transition
({name}`SqlState.publish`) continues with the next state, the next state has the clock of the
state. Proof sketch: only an effect without an error continues, and it changes only the
database. -/
theorem SqlState.publish_clock {state next : SqlState} {position : Nat} {effect : Effect}
    (continued : state.publish position effect = .next next) : next.clock = state.clock := by
  cases effect with
  | ok database => simp only [SqlState.publish, SqlTransition.next.injEq] at continued; subst continued; rfl
  | error failure => simp [SqlState.publish] at continued

/-- For every position, statement, state, effect and next state: if the transition continues
with the next state, the next state has the clock of the state. Proof sketch: a transaction
statement changes only the database and the snapshot; every other statement continues through
{name}`SqlState.publish` ({name}`SqlState.publish_clock`). -/
theorem advanceWith_clock {position : Nat} {statement : Resolved.Statement} {state next : SqlState} {effect : Effect}
    (continued : advanceWith position statement state effect = .next next) : next.clock = state.clock := by
  cases statement <;> first
    | exact SqlState.publish_clock continued
    | (cases snapshot : state.snapshot <;> simp [advanceWith, snapshot] at continued <;> subst continued <;> rfl)

/-- For every position, statement, values, state and next state: if {name}`advance` continues
with the next state, the next state has the clock of the state. Proof sketch: the transition
before the counts continues with a state ({name}`advance_eq_next`), which has the clock
({name}`advanceWith_clock`); the counts change only the counters. -/
theorem advance_clock {position : Nat} {statement : Resolved.Statement} {parameters : List Value}
    {state next : SqlState} (continued : advance position statement parameters state = .next next) :
    next.clock = state.clock := by
  obtain ⟨transitioned, reached, same⟩ := advance_eq_next continued
  have clock := advanceWith_clock reached
  rw [same]
  exact clock

/-- For every connection, resolution state, position, statement and run, the connection after the
statement's transition ({name}`Connection.afterStep`) has the clock of the connection. Proof
sketch: a transition that continues keeps the clock ({name}`advanceWith_clock`), also with the
counts applied; after a halt, {name}`Connection.afterError` builds the state with the connection's
clock. -/
theorem Connection.afterStep_clock (connection : Connection) (after : ResolveState) (position : Nat)
    (statement : Resolved.Statement) (run : StatementRun) :
    (connection.afterStep after run.counts (advanceRun position statement connection.state run)).state.clock =
      connection.state.clock := by
  unfold advanceRun
  cases transition : advanceWith position statement connection.state run.effect with
  | next state => simpa [SqlTransition.counted, Connection.afterStep] using advanceWith_clock transition
  | halt outcome => cases outcome <;> rfl

/-- For every context, optional clock, index, connection, statement and list of values: if the
step with the values continues with an output and a next connection, the next connection has
the clock assignment of the connection, and the output does not end the run
({name}`Output.endsRun`). Proof sketch: {name}`runScriptStep_continued_spec` gives the output and
the connection as {name}`Connection.afterStep` of a transition ({name}`Connection.afterStep_clock`). -/
theorem runScriptStep_continued {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    (continued : runScriptStep context clock index connection statement parameters = .continued output next others) :
    next.state.clock = connection.state.clock ∧ output.endsRun = false := by
  obtain ⟨resolved, after, value, _, _, _, _, _, noStop, rfl, _⟩ := runScriptStep_continued_spec continued
  exact ⟨Connection.afterStep_clock .., noStop⟩

end Belay.Sqlite.Model
