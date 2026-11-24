import Belay

set_option doc.verso true

/-! Temporary witnesses for the control and pragma rules of ADR 0033. The exact rules
prove the original statements with their original premises. -/

namespace Belay.Sqlite.Model.ReplacedControls

/-- The deleted law {lit}`runScriptStep_setting_continues`. For every connection, statement and values that resolve to a setting: the step continues, with no further
execution. Proof sketch: the applicable case of {name}`runScriptStep_setting_eq` gives the result. -/
theorem runScriptStep_setting_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {setting : Syntax.PragmaSetting} {«on» : Bool}
    (found : resolveStatement context connection.resolveState statement = .ok (.setting setting «on», after)) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  rw [runScriptStep_setting_eq found]
  exact ⟨_, _, rfl⟩

/-- The deleted law {lit}`runScriptStep_begin_continues`. For every connection, statement and values that resolve to BEGIN, inside a transaction or outside one: the
step continues, with no further execution. In plain words, the model describes BEGIN in both cases: it opens a
transaction, or fails because one is open. Proof sketch: the applicable case of {name}`runScriptStep_begin_eq` gives the result. -/
theorem runScriptStep_begin_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.begin, after)) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  rw [runScriptStep_begin_eq found]
  split <;> exact ⟨_, _, rfl⟩

/-- The deleted law {lit}`runScriptStep_commit_continues`. For every connection, statement and values that resolve to COMMIT, inside a transaction or outside one: the
step continues, with no further execution. In plain words, the model describes COMMIT in both cases: it closes
the transaction, or fails because none is open. Proof sketch: the applicable case of {name}`runScriptStep_commit_eq` gives the result. -/
theorem runScriptStep_commit_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.commit, after)) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  rw [runScriptStep_commit_eq found]
  split <;> exact ⟨_, _, rfl⟩

/-- The deleted law {lit}`runScriptStep_setting_ok`. For every connection, statement and values that resolve to a setting: the step continues without further
execution, and its output is no error. Proof sketch: the applicable case of {name}`runScriptStep_setting_eq` gives the result. -/
theorem runScriptStep_setting_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {setting : Syntax.PragmaSetting} {«on» : Bool}
    (found : resolveStatement context connection.resolveState statement = .ok (.setting setting «on», after)) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false := by
  rw [runScriptStep_setting_eq found]
  exact ⟨_, _, rfl, rfl⟩

/-- The deleted law {lit}`runScriptStep_begin_ok`. For every connection with no open transaction, statement and values that resolve to BEGIN: the step continues
without further execution, and its output is no error. In plain words, BEGIN outside a transaction succeeds.
Proof sketch: the applicable case of {name}`runScriptStep_begin_eq` gives the result. -/
theorem runScriptStep_begin_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.begin, after))
    (closed : connection.state.snapshot = none) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false := by
  rw [runScriptStep_begin_eq found, closed]
  exact ⟨_, _, rfl, rfl⟩

/-- The deleted law {lit}`runScriptStep_commit_ok`. For every connection with an open transaction, statement and values that resolve to COMMIT: the step
continues without further execution, and its output is no error. In plain words, COMMIT inside a transaction
succeeds. Proof sketch: the applicable case of {name}`runScriptStep_commit_eq` gives the result. -/
theorem runScriptStep_commit_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {original : Database}
    (found : resolveStatement context connection.resolveState statement = .ok (.commit, after))
    (open_ : connection.state.snapshot = some original) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false := by
  rw [runScriptStep_commit_eq found, open_]
  exact ⟨_, _, rfl, rfl⟩

#print axioms runScriptStep_setting_continues
#print axioms runScriptStep_begin_continues
#print axioms runScriptStep_commit_continues
#print axioms runScriptStep_setting_ok
#print axioms runScriptStep_begin_ok
#print axioms runScriptStep_commit_ok

end Belay.Sqlite.Model.ReplacedControls
