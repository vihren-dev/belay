import Belay.Sqlite.Model.ControlStepLaws
import Belay.Sqlite.Model.PragmaStepLaws

set_option doc.verso true

/-! The frame laws of the statements that write no row and change no catalog (ADR 0017, S6): BEGIN,
COMMIT, a setting pragma and a pragma that only reads. A table found by any name is the same table, with
the same rows and at the same position, after each of them. -/

namespace Belay.Sqlite.Model

/-- For every connection and statement that resolves to BEGIN, and every step that continues: the database
of the next connection is the database of the connection, so every name finds the same table with the same
rows. Proof sketch: split on the snapshot; {name}`runScriptStep_begin_idle` and
{name}`runScriptStep_begin_active` give the next connection. -/
theorem runScriptStep_begin_frame {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.begin, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    next.state.database = connection.state.database := by
  cases snapshot : connection.state.snapshot with
  | none => rw [(runScriptStep_begin_idle found snapshot step).2.2]
  | some original => rw [(runScriptStep_begin_active found snapshot step).2.2]

/-- For every connection and statement that resolves to COMMIT, and every step that continues: the
database of the next connection is the database of the connection. Proof sketch: as
{name}`runScriptStep_begin_frame`, with {name}`runScriptStep_commit_active` and
{name}`runScriptStep_commit_idle`. -/
theorem runScriptStep_commit_frame {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.commit, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    next.state.database = connection.state.database := by
  cases snapshot : connection.state.snapshot with
  | none => rw [(runScriptStep_commit_idle found snapshot step).2.2]
  | some original => rw [(runScriptStep_commit_active found snapshot step).2.2]

/-- For every connection and statement that resolves to a setting at a value, and every step that
continues: the database of the next connection is the database of the connection. Proof sketch:
{name}`runScriptStep_setting` gives {name}`Connection.set`, which changes only a setting. -/
theorem runScriptStep_setting_frame {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {setting : Syntax.PragmaSetting} {on : Bool}
    (found : resolveStatement context connection.resolveState statement = .ok (.setting setting on, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    next.state.database = connection.state.database := by
  rw [(runScriptStep_setting found step).2.2]
  cases setting <;> rfl

end Belay.Sqlite.Model
