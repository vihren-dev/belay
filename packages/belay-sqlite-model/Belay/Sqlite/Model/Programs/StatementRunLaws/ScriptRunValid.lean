import Belay.Sqlite.Model.Programs.Scripts.ScriptRunConstraints
import Belay.Sqlite.Model.Schema.Rows.ScriptRunValid

set_option doc.verso true

/-! Runs preserve the validity of a connection's database and transaction snapshot
(ADR 0022, D3, slice 4). The context is in execution mode and uses the profile's limits.
The script theorem covers every statement list; the single-step theorem covers every
step that continues to another connection. -/

namespace Belay.Sqlite.Model

/-- The corollary of the run theorems for {name}`runScriptAllFrom`. For every profile, context in execution mode
with the limits of the profile ({lit}`context.profile.limits = profile.limits`), clock, index, connection and
statements with their values: if the state of the connection satisfies {name}`SqlState.Holds` for
{name}`Database.Valid` (its database, and its snapshot when a transaction is open), the state of the
connection of every complete execution of the script ({lit}`run.connection.state`) satisfies it. It has no hypothesis on the
statements of the script: a CREATE INDEX, an ADD COLUMN, a DROP, a write that cascades, a trigger and a ROLLBACK all keep the
database valid. Proof sketch: apply {name}`runScriptAllFrom_admittedWith` to
{name}`constraintAtoms_statementKeeps`, derive its conditions from admission and the resolver link,
and use {name}`Database.valid_iff` for the start state and the end state. -/
theorem runScriptAllFrom_valid {profile : Profile} (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value))
    (execution : context.mode = .execution) (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.Valid profile)) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds (Database.Valid profile) :=
  fun run member =>
    (runScriptAllFrom_admittedWith constraintAtoms_statementKeeps
      (fun _ _ _ _ statement admitted applied link _ => statement.atomsCondition_of_link admitted applied link)
      context clock index script execution same
      (holds.mono fun _ valid => Database.valid_iff.mp valid) run member).mono fun _ atoms => Database.valid_iff.mpr atoms

/-- The corollary of the run theorems for one statement ({name}`runScriptStep`).
For every profile, context in execution mode with the limits of the profile, clock, index,
connection, statement and values: if the state of the connection satisfies {name}`SqlState.Holds` for
{name}`Database.Valid`, the state of the next connection of every execution of the step
({name}`RunStep.executions`) satisfies it. A step that ends the run has no execution. Proof sketch:
{name}`runScriptAllFrom_valid` for the script of the statement, whose executions are the executions of the
step followed by the empty script. -/
theorem runScriptStep_valid {profile : Profile} (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (statement : Syntax.Statement) (values : List Value)
    (execution : context.mode = .execution) (same : context.profile.limits = profile.limits)
    (holds : connection.state.Holds (Database.Valid profile)) :
    ∀ found ∈ (runScriptStep context clock index connection statement values).executions,
      found.next.state.Holds (Database.Valid profile) := by
  have kept := runScriptAllFrom_valid context clock index [(statement, values)] execution same holds
  intro found member
  cases step : runScriptStep context clock index connection statement values with
  | ended _ => simp [step, RunStep.executions] at member
  | continued output next others =>
    exact kept { outputs := [found.output], connection := found.next }
      (by simp only [runScriptAllFrom, runScriptAllWith, step]
          exact List.mem_flatMap.2 ⟨found, by simpa [step] using member, List.mem_map.2 ⟨⟨[], found.next⟩, by simp [runScriptAllWith], rfl⟩⟩)

end Belay.Sqlite.Model
