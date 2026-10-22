import Belay.Sqlite.Model.ScriptRunIndex

set_option doc.verso true

/-! The run of two scripts one after the other ({lit}`ScriptRun.lean`): the run of {lit}`p ++ q`
is the run of {lit}`p`, then the run of {lit}`q` from the connection that {lit}`p` left, unless
the run of {lit}`p` ends with {name}`Belay.Sqlite.Model.Output.unmodeled`. When the clock of the
connection gives the same value at every position, the run of {lit}`q` is the same from every
index ({lit}`ScriptRunIndex.lean`), so it is the run of {lit}`q` on its own. -/

namespace Belay.Sqlite.Model

/-- For every context, index, connection and statements, the connection at the end of the run
({name}`runScriptFrom`) has the clock of the connection at its start. Proof sketch: induction on
the statements; each step that continues keeps the clock ({name}`runScriptStep_continued`). -/
theorem runScriptFrom_clock (context : ResolveContext) (index : Nat) (connection : Connection)
    (statements : List Syntax.Statement) :
    (runScriptFrom context index connection statements).connection.state.clock = connection.state.clock := by
  induction statements generalizing index connection with
  | nil => rfl
  | cons statement rest later =>
    simp only [runScriptFrom]
    split
    · rfl
    · rename_i output next continued
      rw [later, (runScriptStep_continued continued).1]

/-- For every context, two indexes, connection and statements: if the clock of the connection
gives the same value at every position, the run from the first index is the run from the second.
Proof sketch: induction on the statements; each step is the same at both indexes
({name}`runScriptStep_index`), and the next connection keeps the clock
({name}`runScriptStep_continued`). -/
theorem runScriptFrom_index (context : ResolveContext) (first second : Nat) (connection : Connection)
    (statements : List Syntax.Statement)
    (constant : ∀ one other, connection.state.clock one = connection.state.clock other) :
    runScriptFrom context first connection statements = runScriptFrom context second connection statements := by
  induction statements generalizing first second connection with
  | nil => rfl
  | cons statement rest later =>
    simp only [runScriptFrom, runScriptStep_index context first second connection statement (constant _ _)]
    split
    · rfl
    · rename_i output next continued
      have kept := (runScriptStep_continued continued).1
      rw [later (first + 1) (second + 1) next (fun one other => by rw [kept]; exact constant one other)]

/-- Whether the run ended at a statement that the model does not describe: one of its outputs
ends the run ({name}`Output.endsRun`). For example, {assert}`!({ outputs := [], connection :=
{ state := { database := {} } } } : ScriptRun).ended`. -/
def ScriptRun.ended (run : ScriptRun) : Bool := run.outputs.any Output.endsRun

/-- The run, then the later run from the connection at its end, unless the run ended
({name}`ScriptRun.ended`): the outputs of both, and the later run's connection. -/
def ScriptRun.andThen (run : ScriptRun) (later : Connection → ScriptRun) : ScriptRun :=
  if run.ended then run
  else
    let next := later run.connection
    { outputs := run.outputs ++ next.outputs, connection := next.connection }

/-- For every context, index, connection and statements {lit}`p` and {lit}`q`: the run of
{lit}`p ++ q` from the index is the run of {lit}`p`, then ({name}`ScriptRun.andThen`) the run of
{lit}`q` from the index after {lit}`p`, on the connection that {lit}`p` left. When the run of
{lit}`p` ends with {name}`Output.unmodeled`, it is the run of {lit}`p` alone. Proof sketch:
induction on {lit}`p`; a step that continues gives an output that does not end the run
({name}`runScriptStep_continued`), so the run after it ends exactly when the rest does. -/
theorem runScriptFrom_append (context : ResolveContext) (index : Nat) (connection : Connection)
    (p q : List Syntax.Statement) :
    runScriptFrom context index connection (p ++ q) =
      (runScriptFrom context index connection p).andThen (runScriptFrom context (index + p.length) · q) := by
  induction p generalizing index connection with
  | nil => simp [runScriptFrom, ScriptRun.andThen, ScriptRun.ended]
  | cons statement rest later =>
    simp only [List.cons_append, runScriptFrom]
    split
    · simp [ScriptRun.andThen, ScriptRun.ended, Output.endsRun]
    · rename_i output next continued
      have quiet := (runScriptStep_continued continued).2
      rw [later (index + 1) next]
      simp only [ScriptRun.andThen, ScriptRun.ended, List.any_cons, quiet, Bool.false_or, List.length_cons,
        Nat.add_assoc, Nat.add_comm 1 rest.length]
      split <;> rfl

/-- For every context, index, connection and statements {lit}`p` and {lit}`q`: if the clock of
the connection gives the same value at every position, the run of {lit}`p ++ q` from the index
is the run of {lit}`p`, then ({name}`ScriptRun.andThen`) the run of {lit}`q` from index 0, on the
connection that {lit}`p` left. Proof sketch: {name}`runScriptFrom_append`, and the run of
{lit}`q` does not depend on its index ({name}`runScriptFrom_index`), because the connection
that {lit}`p` left has the same clock ({name}`runScriptFrom_clock`). -/
theorem runScriptFrom_append_constant (context : ResolveContext) (index : Nat) (connection : Connection)
    (p q : List Syntax.Statement)
    (constant : ∀ one other, connection.state.clock one = connection.state.clock other) :
    runScriptFrom context index connection (p ++ q) =
      (runScriptFrom context index connection p).andThen (runScriptFrom context 0 · q) := by
  rw [runScriptFrom_append]
  simp only [ScriptRun.andThen]
  split
  · rfl
  · rw [runScriptFrom_index context (index + p.length) 0 _ q (by
      intro one other; rw [runScriptFrom_clock]; exact constant one other)]

end Belay.Sqlite.Model
