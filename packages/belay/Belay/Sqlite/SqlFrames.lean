import Belay.Sqlite.ExecutionBind
import Belay.Sqlite.SendStatementsBranches

set_option doc.verso true

/-!
Frames of programs (ADR 0017, S6). A frame claim says that an observation of the connection, for example
the rows of one table, is the same at the end of every branch of a program as at its start. Branches
include every execution of every statement, every permitted choice of an output that is a choice between
results, and every stop. The rules compose the claim over a program by its structure: a pure program,
one statement and the rest, a sequence. Each rule takes the facts about one step as a premise, so a rule
for a family of statements, such as plain writes to other tables, supplies them.
-/

namespace Belay.Sqlite
open Model

/-- The frame claim for a program at a context: on every branch of the program from the context, the
observation of the final connection equals the observation of the connection of the context. In plain
words, nothing that the observation sees changes on any branch, whatever the outputs that a branch
chooses, and also when the program stops early. The observation is any function of the connection, so a
pair of observations is one observation. For example, observing the rows of one table claims that the program
does not write that table. -/
def Sql.Frame {α β : Type} (program : Sql α) (observe : Connection → β) (state : ExecutionContext) : Prop :=
  ∀ result, program.Branch state.clock state.index state.connection result →
    observe result.connection = observe state.connection

/-- A pure program keeps every observation. Proof sketch: its only branch keeps the connection. -/
theorem Sql.Frame.pure {α β : Type} (value : α) (observe : Connection → β) (state : ExecutionContext) :
    (Sql.pure value).Frame observe state := by
  intro result branch
  rw [(Sql.branch_pure_iff _ _ _ _ _).mp branch]

/-- For every statement, values, continuation and observation: the program that sends the statement and
continues keeps the observation if, for every continuing step of the statement and every execution of the
step, the execution keeps the observation, and the continuation, for every permitted choice of an output, keeps
it from the context after that execution. A step that stops the run needs no premise: it keeps the
connection. In plain words, a frame claim about a statement and what follows needs the effect of the
statement on the observation, once for each of its executions, and the claim for the rest.
Proof sketch: invert the branch. A stop keeps the connection. A continued branch passes through the chosen
execution, which keeps the observation, to a branch of the continuation, which keeps it by premise. -/
theorem Sql.Frame.exec {α β : Type} {statement : Syntax.Statement} {values : List Value}
    {rest : Output → Sql α} {observe : Connection → β} {state : ExecutionContext}
    (keeps : ∀ actual next others,
      runScriptStep runContext state.clock state.index state.connection statement values =
        .continued actual next others →
      ∀ found ∈ (RunStep.continued actual next others).executions,
        observe found.next = observe state.connection ∧
        ∀ selected, OutputChoice found.output selected →
          (rest selected).Frame observe (state.next selected found.next)) :
    (Sql.exec statement values rest).Frame observe state := by
  intro result branch
  cases branch with
  | stopped step => rfl
  | continued step member choice later =>
    obtain ⟨moved, rest⟩ := keeps _ _ _ step _ member
    exact (rest _ choice _ later).trans moved

/-- For every program, continuation and observation: the program followed by the continuation keeps the
observation if the program keeps it, and the continuation keeps it from the context after every branch of the
program that returns a value, for that value. A branch that stops needs nothing more, because the
continuation does not run. Proof sketch: split the branch of the sequence into a branch of the program and a
branch of the continuation ({name}`Sql.branch_bind_iff`) and join the two claims. -/
theorem Sql.Frame.bind {α γ β : Type} {program : Sql α} {next : α → Sql γ} {observe : Connection → β}
    {state : ExecutionContext}
    (first : program.Frame observe state)
    (second : ∀ ran, program.Branch state.clock state.index state.connection ran → ∀ value, ran.value = some value →
      (next value).Frame observe (state.finish ran)) :
    (program.bind next).Frame observe state := by
  intro result branch
  obtain ⟨ran, ranBranch, split⟩ := (Sql.branch_bind_iff program next _ _ _ result).mp branch
  have moved := first ran ranBranch
  cases hasValue : ran.value with
  | none => rw [hasValue] at split; subst split; exact moved
  | some value =>
    rw [hasValue] at split
    obtain ⟨last, lastBranch, rfl⟩ := split
    exact (second ran ranBranch value hasValue last lastBranch).trans moved

/-- For every program, function and observation: mapping the value of a program keeps the observation if the
program keeps it. Proof sketch: a branch of the mapped program is a branch of the program with a mapped value
({name}`Sql.branch_map_iff`). -/
theorem Sql.Frame.map {α γ β : Type} {program : Sql α} {function : α → γ} {observe : Connection → β}
    {state : ExecutionContext} (frame : program.Frame observe state) :
    (program.map function).Frame observe state := by
  intro result branch
  obtain ⟨first, firstBranch, rfl⟩ := (Sql.branch_map_iff function program _ _ _ result).mp branch
  exact frame first firstBranch

/-- For every program, observation and function of the observation: a frame claim for the observation gives
the claim for the function of it. In plain words, a claim about the rows and the catalog together gives the claim
about the rows alone. Proof sketch: equal observations have equal images. -/
theorem Sql.Frame.comp {α β γ : Type} {program : Sql α} {observe : Connection → β} {state : ExecutionContext}
    (frame : program.Frame observe state) (coarser : β → γ) : program.Frame (coarser ∘ observe) state := by
  intro result branch
  exact congrArg coarser (frame result branch)

end Belay.Sqlite
