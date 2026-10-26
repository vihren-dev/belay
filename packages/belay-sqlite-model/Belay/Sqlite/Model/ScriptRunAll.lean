import Belay.Sqlite.Model.ScriptRun

set_option doc.verso true

/-! The complete executions of a script (ADR 0019, D4, amended 2026-10-25). A statement can have
several possible executions ({name}`Belay.Sqlite.Model.RunStep.executions`), and a later statement
runs from the connection of the execution that reached it. A complete execution of a script is one
sequence of statement executions, one for each statement that it reached: it never combines the
output of one execution of a statement with the connection of another, and it never takes the first
statement from one execution and the second from another.
{name}`Belay.Sqlite.Model.runScriptFrom` is the traversal that follows the model's own execution
of each statement; this module lists all complete executions, and
{lit}`runScriptFrom_mem_runScriptAllFrom` shows that the traversal is one of them. -/

namespace Belay.Sqlite.Model

/-- The complete executions of the statements from a zero-based index on a connection, for a function
that gives the step of each statement ({name}`RunStep`) at its index on its connection. A statement
that ends the run gives one execution with the output {name}`Output.unmodeled`; a statement
that continues gives, for each of its executions, the executions of the rest from the connection of
that execution, each with the output of that execution first. The function argument lets a caller
run the executions of a statement that it describes itself. -/
def runScriptAllWith (step : Nat → Connection → Syntax.Statement × List Value → RunStep) :
    Nat → Connection → List (Syntax.Statement × List Value) → List ScriptRun
  | _, connection, [] => [{ outputs := [], connection }]
  | index, connection, entry :: rest =>
    match step index connection entry with
    | .ended reason => [{ outputs := [.unmodeled reason], connection }]
    | stepped@(.continued ..) =>
      stepped.executions.flatMap fun execution =>
        (runScriptAllWith step (index + 1) execution.next rest).map fun later =>
          { later with outputs := execution.output :: later.outputs }

/-- All complete executions of the statements with their values, from a zero-based index on the
connection, with an optional clock: {name}`runScriptAllWith` with the step {name}`runScriptStep`. -/
def runScriptAllFrom (context : ResolveContext) (clock : Option Clock) (index : Nat) (connection : Connection)
    (script : List (Syntax.Statement × List Value)) : List ScriptRun :=
  runScriptAllWith (fun index connection (statement, parameters) =>
    runScriptStep context clock index connection statement parameters) index connection script

/-- For every context, optional clock, index, connection and statements with their values, the run of
the model's own traversal ({name}`runScriptFrom`) is one of the complete executions
({name}`runScriptAllFrom`). It holds also when a statement has more than one execution, because the
first execution of each step is the model's own. Proof sketch: induction on the statements; the model's
own execution is the first execution of the step, and the rest of the traversal is one of the
executions from its connection. -/
theorem runScriptFrom_mem_runScriptAllFrom (context : ResolveContext) (clock : Option Clock) :
    ∀ (index : Nat) (connection : Connection) (script : List (Syntax.Statement × List Value)),
      runScriptFrom context clock index connection script ∈ runScriptAllFrom context clock index connection script
  | _, _, [] => by simp [runScriptFrom, runScriptAllFrom, runScriptAllWith]
  | index, connection, (statement, parameters) :: rest => by
    unfold runScriptFrom runScriptAllFrom
    cases step : runScriptStep context clock index connection statement parameters with
    | ended reason => simp [runScriptAllWith, step]
    | continued output next others =>
      simp only [runScriptAllWith, step, RunStep.executions, List.flatMap_cons, List.mem_append, List.mem_map]
      exact Or.inl ⟨_, by simpa [runScriptAllFrom] using runScriptFrom_mem_runScriptAllFrom context clock (index + 1) next rest, rfl⟩

end Belay.Sqlite.Model
