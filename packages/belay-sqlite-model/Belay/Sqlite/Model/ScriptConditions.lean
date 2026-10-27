import Belay.Sqlite.Model.ScriptRun

set_option doc.verso true

/-! The conditions that a script puts on the statements that its run reaches (ADR 0022, D3; ADR 0019,
D4, amended 2026-10-25). A statement can have several possible executions, and a later statement runs
from the connection of the execution that reached it, so the condition of the rest of the script is
asked for the connection of each execution. -/

namespace Belay.Sqlite.Model

/-- For the given condition of statements on a database, context, clock, index, connection and
statements with their values, each statement that {name}`runScriptFrom` resolves meets the
condition on the database of the connection before it:

* the empty list requires nothing;
* a list with a first statement requires, for each resolved statement and state that
  {name}`resolveStatement` gives for the first statement over the connection, the condition of
  the resolved statement on the database of the connection; and, when
  {name}`runScriptStep` continues, the conditions of the rest from the next index and the
  connection of each execution of the statement ({name}`RunStep.executions`). A statement at which
  the run ends requires nothing of the rest, and a statement that does not resolve requires no
  condition. -/
def ScriptConditionsWith (condition : Resolved.Statement → Database → Prop) (context : ResolveContext)
    (clock : Option Clock) (index : Nat) (connection : Connection) :
    List (Syntax.Statement × List Value) → Prop
  | [] => True
  | (statement, parameters) :: rest =>
    (∀ resolved after, resolveStatement context connection.resolveState statement = .ok (resolved, after) →
      condition resolved connection.state.database) ∧
      match runScriptStep context clock index connection statement parameters with
      | .ended _ => True
      | stepped@(.continued ..) =>
        ∀ execution ∈ stepped.executions, ScriptConditionsWith condition context clock (index + 1) execution.next rest

end Belay.Sqlite.Model
