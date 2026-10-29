import Belay.Sqlite.Model.ScriptRun
import Belay.Sqlite.Model.RunHolds

set_option doc.verso true

/-! Conditions follow every reached execution, with its selected clock, visible counters and
parameters. An invariant guard admits obligations derived from the current state. -/

namespace Belay.Sqlite.Model

/-- For the given surface step, each successful resolution with a selected clock and a supported
state run meets the condition on its actual evaluator inputs. A failed resolution, missing clock
or failed support gate requires nothing. Use a condition that ignores unused inputs. -/
def ScriptStepCondition (condition : StatementCondition) (context : ResolveContext) (clock : Option Clock)
    (index : Nat) (connection : Connection) (statement : Syntax.Statement) (parameters : List Value) : Prop :=
  ∀ resolved after value,
    resolveStatement context connection.resolveState statement = .ok (resolved, after) →
    statementClock clock index resolved = some value →
    (connection.state.statementRun value parameters resolved).ready = true →
    condition value (connection.state.counters.view resolved.counterReads) parameters resolved connection.state.database

/-- For the given invariant and execution condition, each reached step meets its condition when
its current database and snapshot have the invariant. The rest is required for every continuing
execution's next connection. Empty scripts and suffixes after ended steps require nothing.
A state without the invariant requires no head condition; its continuing suffix is still checked. -/
def ScriptConditionsWith (property : Database → Prop) (condition : StatementCondition)
    (context : ResolveContext) (clock : Option Clock) (index : Nat) (connection : Connection) :
    List (Syntax.Statement × List Value) → Prop
  | [] => True
  | (statement, parameters) :: rest =>
    (connection.state.Holds property → ScriptStepCondition condition context clock index connection statement parameters) ∧
      match runScriptStep context clock index connection statement parameters with
      | .ended _ => True
      | stepped@(.continued ..) =>
        ∀ execution ∈ stepped.executions,
          ScriptConditionsWith property condition context clock (index + 1) execution.next rest

/-- If every step on every state with the invariant meets its execution condition, every script
meets the guarded reached conditions from every index and connection. This constructs obligations;
it assumes no preservation theorem. Proof sketch: supply the head implication and follow all next connections. -/
theorem ScriptConditionsWith.of_invariant {property : Database → Prop} {condition : StatementCondition}
    (context : ResolveContext) (clock : Option Clock)
    (derive : ∀ index connection statement parameters, connection.state.Holds property →
      ScriptStepCondition condition context clock index connection statement parameters) :
    ∀ index connection script, ScriptConditionsWith property condition context clock index connection script
  | _, _, [] => trivial
  | index, connection, (statement, parameters) :: rest => by
    refine ⟨derive index connection statement parameters, ?_⟩
    cases runScriptStep context clock index connection statement parameters with
    | ended _ => trivial
    | continued output next others =>
      exact fun execution _ => ScriptConditionsWith.of_invariant context clock derive (index + 1) execution.next rest

end Belay.Sqlite.Model
