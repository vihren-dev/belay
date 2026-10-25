import Belay.Sqlite.ExecutionContext

set_option doc.verso true

namespace Belay.Sqlite

/-- An observation annotation for one exact program. Each step specifies whether to hide
its successful output, and supplies an annotation for every output-dependent continuation.
For an ordinary observation use {lit}`Sql.View.identity`; for a migration segment use
{lit}`Sql.View.quiet`. Compose segment witnesses with {lit}`Sql.View.bind`. -/
inductive Sql.View {α : Type} : Sql α → Type where
  /-- A pure return contributes no statement output to the observation. -/
  | pure (value : α) : View (.pure value)
  /-- Annotate one step and each possible continuation. Errors and stopping reasons remain
  observable even when the successful output is hidden. -/
  | exec {statement values rest} (hideSuccessful : Bool)
      (later : ∀ output, View (rest output)) : View (.exec statement values rest)

/-- Apply the same annotation to every step, including every result-dependent branch.
Use false to retain all outputs, or true to hide successful outputs of this segment. -/
def Sql.View.uniform {α : Type} (hideSuccessful : Bool) : (program : Sql α) → View program
  | .pure value => .pure value
  | .exec _ _ rest => .exec hideSuccessful fun output => uniform hideSuccessful (rest output)

/-- Observe every output of the program. For example, this is the default annotation for
application statements surrounding a migration. -/
def Sql.View.identity {α : Type} (program : Sql α) : View program := uniform false program

/-- Hide the successful statement outputs of this program when projecting its trace.
Errors, stops and the program's return value remain visible. This is an observation
descriptor; executing the original program still produces all its outputs. -/
def Sql.View.quiet {α : Type} (program : Sql α) : View program := uniform true program

/-- Annotate a bind with the first segment's view and a view for every returned value's
continuation. A stopped first segment never reaches the continuation. Use this to identify
a migration chosen from an earlier result without searching its output values. -/
def Sql.View.bind {α β : Type} {program : Sql α} (view : View program)
    (next : α → Sql β) (later : ∀ value, View (next value)) : View (program.bind next) :=
  match view with
  | .pure value => later value
  | .exec hideSuccessful rest => .exec hideSuccessful fun output => (rest output).bind next later

/-- Erase the annotation to its original program. Running this value uses the ordinary
interpreter, with the same values, outputs and complete connection state. -/
def Sql.View.erase {α : Type} {program : Sql α} (_view : View program) : Sql α := program

/-- For every annotation and starting clock, index and connection, interpreting its erased
program gives exactly the ordinary run. Proof sketch: erasure is the original program. -/
theorem Sql.View.erase_runFrom {α : Type} {program : Sql α} (view : View program)
    (clock : Option Model.Clock) (index : Nat) (connection : Model.Connection) :
    view.erase.runFrom clock index connection = program.runFrom clock index connection := rfl

end Belay.Sqlite
