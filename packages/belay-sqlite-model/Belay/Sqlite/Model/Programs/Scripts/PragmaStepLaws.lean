import Belay.Sqlite.Model.Programs.Scripts.ReadOnlyFrame
import Belay.Sqlite.Model.Programs.Scripts.OrdinaryStepEffects
import Belay.Sqlite.Model.Schema.Rows.PragmaStepLaws

set_option doc.verso true

/-! The step laws of the pragmas (ADR 0017, S6). A pragma that only reads, such as
{lit}`PRAGMA foreign_key_check`, resolves to a query or a prepare error, so a step of it keeps the
connection. A pragma that sets a setting changes the setting of the connection and nothing else. -/

namespace Belay.Sqlite.Model

/-- For every connection and statement of a pragma that only reads, such as {lit}`PRAGMA foreign_key_check`,
and every step that continues: the step has no further execution and the next connection is the
connection. In plain words, a pragma without a value changes nothing, not even the counters, also
when it fails as a prepare error. Proof sketch: {name}`resolveStatementPragma_readOnly` shows that the
resolved statement is a query or a prepare error, and {name}`runScriptStep_readOnly_keeps` applies. -/
theorem runScriptStep_pragma_keeps {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {pragma : Syntax.Pragma} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {resolved : Resolved.Statement} {after : ResolveState} (reads : pragma.readsOnly = true)
    (found : resolveStatement context connection.resolveState (.pragma pragma) = .ok (resolved, after))
    (step : runScriptStep context clock index connection (.pragma pragma) parameters = .continued output next others) :
    others = [] ∧ next = connection :=
  runScriptStep_readOnly_keeps found
    (resolveStatementPragma_readOnly reads (by simpa only [statement_arms] using found)) step

/-- The connection with a setting at a value: {name}`ResolveState.set` for the connection. For example, the
setting {lit}`foreign_keys` at {lean}`true` turns enforcement on and leaves the database, the transaction
and the counters as they are. -/
def Connection.set (connection : Connection) (on : Bool) : Syntax.PragmaSetting → Connection
  | .foreignKeys => { connection with foreignKeys := on }
  | .recursiveTriggers => { connection with recursiveTriggers := on }

/-- For every connection and statement that resolves to a setting at a value, and every step that
continues: the step has no error output and no further execution, and the next connection is the
connection with the setting at the value ({name}`Connection.set`). In plain words, a setting changes
the setting and nothing else: the database, the open transaction, the clock assignment and the counters
stay (failure law: it never fails; success law: the new connection). Proof sketch: the statement is no
query and the transition continues, so the output is no error
({name}`Output.ofStep_isError_of_noHalt`); the transition keeps the state and
{name}`resolveStatement_certificate` gives the settings. -/
theorem runScriptStep_setting {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {setting : Syntax.PragmaSetting} {on : Bool}
    (found : resolveStatement context connection.resolveState statement = .ok (.setting setting on, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = false ∧ others = [] ∧ next = connection.set on setting := by
  obtain ⟨resolved, after', value, same, -, -, -, ofStep, -, nextEq, -⟩ := runScriptStep_continued_spec step
  rw [found] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
  have afterEq := (resolveStatement_certificate context _ _ _ _ found).after
  refine ⟨?_, runScriptStep_others step found rfl, ?_⟩
  · rw [← ofStep]
    exact Output.ofStep_isError_of_noHalt _ _ _ _ _ _ _ (by intro _ _ same; cases same)
      (by simp [advanceRun, advanceWith, SqlTransition.counted, SqlState.publish, haltError, SqlState.statementRun,
        runStatement, Model.step])
  · rw [nextEq, afterEq]
    cases setting <;>
    · simp [advanceRun, advanceWith, SqlTransition.counted, SqlState.publish, Connection.afterStep,
        SqlState.statementRun, runStatement, Model.step, ResolveState.after, ResolveState.set, Connection.set,
        Connection.resolveState]

/-- For every connection, truth value and statement {lit}`PRAGMA foreign_keys = value` that resolves, and every
step that continues: the next connection is the connection with enforcement at the value outside a
transaction, and with enforcement as it was inside one. In plain words, a new connection has
enforcement off, as in SQLite, and the pragma turns it on only when no transaction is open. The step has no
error output and no further execution. Proof sketch: {name}`resolvePragma` resolves the pragma to a
setting at the value outside a transaction and at the old value inside one, and
{name}`runScriptStep_setting` reads the step; the snapshot of the connection is the saved catalog of the
resolution state. -/
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
  exact runScriptStep_setting found step

end Belay.Sqlite.Model
