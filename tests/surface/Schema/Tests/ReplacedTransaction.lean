import Belay

set_option doc.verso true

/-! Temporary witnesses for the control and pragma rules of ADR 0033. The exact rules
prove the original statements with their original premises. -/

namespace Belay.Sqlite.Model.ReplacedControls

/-- The deleted law {lit}`runScriptStep_begin_idle`. For every connection and BEGIN statement that resolves to BEGIN, and every step that continues outside
a transaction: the step has no error output and no further execution, and the next connection is the
connection with the snapshot of the database before. In plain words, BEGIN records the database as
the committed one and changes nothing else (success law). Proof sketch: the applicable case of {name}`runScriptStep_begin_eq` gives the result. -/
theorem runScriptStep_begin_idle {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.begin, after))
    (idle : connection.state.snapshot = none)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = false ∧ others = [] ∧
      next = { connection with state := { connection.state with snapshot := some connection.state.database } } := by
  rw [runScriptStep_begin_eq found, idle] at step
  cases step; exact ⟨rfl, rfl, rfl⟩

/-- The deleted law {lit}`runScriptStep_begin_active`. For every connection and statement that resolves to BEGIN, and every step that continues inside a
transaction: the step has an error output and no further execution, and the next connection is the
connection. In plain words, BEGIN inside a transaction fails and changes nothing, not even the counters
(failure law). Proof sketch: the applicable case of {name}`runScriptStep_begin_eq` gives the result. -/
theorem runScriptStep_begin_active {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {original : Database}
    (found : resolveStatement context connection.resolveState statement = .ok (.begin, after))
    (active : connection.state.snapshot = some original)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = true ∧ others = [] ∧ next = connection := by
  rw [runScriptStep_begin_eq found, active] at step
  cases step; exact ⟨rfl, rfl, rfl⟩

/-- The deleted law {lit}`runScriptStep_commit_active`. For every connection and statement that resolves to COMMIT, and every step that continues inside a
transaction: the step has no error output and no further execution, and the next connection is the
connection without the snapshot. In plain words, COMMIT keeps the database as it is and closes the
transaction (success law). Proof sketch: the applicable case of {name}`runScriptStep_commit_eq` gives the result. -/
theorem runScriptStep_commit_active {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {original : Database}
    (found : resolveStatement context connection.resolveState statement = .ok (.commit, after))
    (active : connection.state.snapshot = some original)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = false ∧ others = [] ∧
      next = { connection with state := { connection.state with snapshot := none } } := by
  rw [runScriptStep_commit_eq found, active] at step
  cases step; exact ⟨rfl, rfl, rfl⟩

/-- The deleted law {lit}`runScriptStep_commit_idle`. For every connection and statement that resolves to COMMIT, and every step that continues outside a
transaction: the step has an error output and no further execution, and the next connection is the
connection. In plain words, COMMIT without a transaction fails and changes nothing (failure law). Proof
sketch: the idle case of {name}`runScriptStep_commit_eq` gives the result. -/
theorem runScriptStep_commit_idle {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.commit, after))
    (idle : connection.state.snapshot = none)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = true ∧ others = [] ∧ next = connection := by
  rw [runScriptStep_commit_eq found, idle] at step
  cases step; exact ⟨rfl, rfl, rfl⟩

#print axioms runScriptStep_begin_idle
#print axioms runScriptStep_begin_active
#print axioms runScriptStep_commit_active
#print axioms runScriptStep_commit_idle

end Belay.Sqlite.Model.ReplacedControls
