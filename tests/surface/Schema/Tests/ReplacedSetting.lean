import Belay

set_option doc.verso true

/-! Temporary witnesses for the control and pragma rules of ADR 0033. The exact rules
prove the original statements with their original premises. -/

namespace Belay.Sqlite.Model.ReplacedControls

/-- The deleted law {lit}`runScriptStep_setting`. For every connection and statement that resolves to a setting at a value, and every step that
continues: the step has no error output and no further execution, and the next connection is the
connection with the setting at the value ({name}`Connection.set`). In plain words, a setting changes
the setting and nothing else: the database, the open transaction, the clock assignment and the counters
stay (failure law: it never fails; success law: the new connection). Proof sketch: the applicable case of {name}`runScriptStep_setting_eq` gives the result. -/
theorem runScriptStep_setting {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {setting : Syntax.PragmaSetting} {«on» : Bool}
    (found : resolveStatement context connection.resolveState statement = .ok (.setting setting «on», after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = false ∧ others = [] ∧ next = connection.set «on» setting := by
  rw [runScriptStep_setting_eq found] at step
  cases step; exact ⟨rfl, rfl, rfl⟩

/-- The deleted law {lit}`runScriptStep_pragma_foreignKeys`. For every connection, truth value and statement {lit}`PRAGMA foreign_keys = value` that resolves, and every
step that continues: the next connection is the connection with enforcement at the value outside a
transaction, and with enforcement as it was inside one. In plain words, a new connection has
enforcement off, as in SQLite, and the pragma turns it on only when no transaction is open. The step has no
error output and no further execution. Proof sketch: the applicable case of {name}`runScriptStep_setting_eq` gives the result. -/
theorem runScriptStep_pragma_foreignKeys {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {parameters : List Value} {output : Output} {others : List StatementExecution}
    {resolved : Resolved.Statement} {after : ResolveState} {value : Bool}
    (found : resolveStatement context connection.resolveState (.pragma (.setting .foreignKeys (some value))) =
      .ok (resolved, after))
    (step : runScriptStep context clock index connection (.pragma (.setting .foreignKeys (some value))) parameters =
      .continued output next others) :
    output.isError = false ∧ others = [] ∧
      next = { connection with foreignKeys := if connection.state.snapshot.isSome then connection.foreignKeys else value } := by
  have resolution : resolved = .setting .foreignKeys
      (if connection.state.snapshot.isSome then connection.foreignKeys else value) := by
    simp only [statement_arms, resolveStatementPragma, resolvePragma, Except.ok.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, -⟩ := found
    simp [Connection.resolveState]
  subst resolution
  rw [runScriptStep_setting_eq found] at step
  cases step; exact ⟨rfl, rfl, rfl⟩

#print axioms runScriptStep_setting
#print axioms runScriptStep_pragma_foreignKeys

end Belay.Sqlite.Model.ReplacedControls
