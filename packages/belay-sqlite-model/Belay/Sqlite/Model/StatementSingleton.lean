import Belay.Sqlite.Model.StatementStep

set_option doc.verso true

/-! Every statement that the model describes today has one next state (ADR 0019, D4, amended
2026-10-25): its run lists no further execution ({name}`Belay.Sqlite.Model.StatementRun.alternatives`). A query can
still have several permitted results on that one state ({lit}`Output.oneOf`). A statement whose
result depends on the plan of SQLite gives alternatives in its run, and then this theorem no longer
covers it. -/

namespace Belay.Sqlite.Model

/-- For every run that {name}`StatementRun.withKeys` builds, the run has no alternative. Proof sketch:
the cases of the optional run of the keys build a run with the default alternatives. -/
theorem StatementRun.withKeys_alternatives (effect : Effect) (ready : Bool) (counts : Counts) (keys : Option KeyRun) :
    (StatementRun.withKeys effect ready counts keys).alternatives = [] := by
  cases keys <;> rfl

/-- For every clock, counters, values, statement, database and initial database, the run of the
statement ({name}`runStatement`) has no alternative execution: each statement that the model
supports today has one next state, the database, counters and connection of its own run. The
output is the output of that run; a query keeps its permitted results in {lit}`Output.oneOf`. Proof sketch: a
case split on the statement and on the table that it writes; each run is a record with the default
alternatives, or a run built by {name}`StatementRun.withKeys`. -/
theorem runStatement_alternatives (clock : Int) (counters : Counters) (parameters : List Value)
    (statement : Resolved.Statement) (database : Database) (initial : Option Database) :
    (runStatement clock counters parameters statement database initial).alternatives = [] := by
  unfold runStatement
  split <;> (try split) <;> simp [StatementRun.withKeys_alternatives]

/-- For every state, clock, values and statement, the run of the statement on a connection state
({name}`SqlState.statementRun`) has no alternative execution. Proof sketch: {name}`runStatement_alternatives`;
the support check changes only {lit}`ready`. -/
theorem SqlState.statementRun_alternatives (state : SqlState) (clock : Int) (parameters : List Value)
    (statement : Resolved.Statement) (initial : Option Database) :
    (state.statementRun clock parameters statement initial).alternatives = [] :=
  runStatement_alternatives ..

end Belay.Sqlite.Model
