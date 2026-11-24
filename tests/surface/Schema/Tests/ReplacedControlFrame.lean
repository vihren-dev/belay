import Belay

set_option doc.verso true

/-! Temporary witnesses for the control and pragma rules of ADR 0033. The exact rules
prove the original statements with their original premises. -/

namespace Belay.Sqlite.Model.ReplacedControls

/-- The deleted law {lit}`runScriptStep_begin_frame`. For every connection and statement that resolves to BEGIN, and every step that continues: the database
of the next connection is the database of the connection, so every name finds the same table with the same
rows. Proof sketch: the applicable case of {name}`runScriptStep_begin_eq` gives the result. -/
theorem runScriptStep_begin_frame {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.begin, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    next.state.database = connection.state.database := by
  rw [runScriptStep_begin_eq found] at step
  split at step <;> cases step <;> rfl

/-- The deleted law {lit}`runScriptStep_commit_frame`. For every connection and statement that resolves to COMMIT, and every step that continues: the
database of the next connection is the database of the connection. Proof sketch: the applicable case of {name}`runScriptStep_commit_eq` gives the result. -/
theorem runScriptStep_commit_frame {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.commit, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    next.state.database = connection.state.database := by
  rw [runScriptStep_commit_eq found] at step
  split at step <;> cases step <;> rfl

/-- The deleted law {lit}`runScriptStep_setting_frame`. For every connection and statement that resolves to a setting at a value, and every step that
continues: the database of the next connection is the database of the connection. Proof sketch: the applicable case of {name}`runScriptStep_setting_eq` gives the result. -/
theorem runScriptStep_setting_frame {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {setting : Syntax.PragmaSetting} {«on» : Bool}
    (found : resolveStatement context connection.resolveState statement = .ok (.setting setting «on», after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    next.state.database = connection.state.database := by
  rw [runScriptStep_setting_eq found] at step
  cases step; cases setting <;> rfl

#print axioms runScriptStep_begin_frame
#print axioms runScriptStep_commit_frame
#print axioms runScriptStep_setting_frame

end Belay.Sqlite.Model.ReplacedControls
