import Belay.Sqlite.ExecutionContext

set_option doc.verso true

namespace Belay.Sqlite
open Model

/-- A permitted observation of one continued step is its actual raw output, or a concrete
rows result listed by an actual {name}`Output.oneOf`. Repetition does not add observations;
an empty list still permits the raw wrapper. Other outputs permit only themselves. -/
def OutputChoice (actual selected : Output) : Prop :=
  selected = actual ∨ match actual with
    | .oneOf alternatives => ∃ rows ∈ alternatives, selected = .rows rows
    | .done _ | .rows _ | .error _ | .unmodeled _ => False

/-- A complete execution branch from the supplied clock, index and full connection.
Pure returns immediately. A stopping model step retains its reason and connection and
returns no value. A continued step chooses one of the executions of its statement
({name}`RunStep.executions`) and an allowed observation of that execution's output, passes the
observation to the continuation, which runs from the connection of that execution, and records the
observation in the trace. SQL errors continue in the same way as other modeled outputs. Every step
uses {name}`runScriptStep`; this relation adds no evaluator. -/
inductive Sql.Branch {α : Type} : Sql α → Option Clock → Nat → Connection → SqlRun α → Prop where
  /-- Pure returns its value without changing the connection or producing an output. -/
  | pure (value : α) (clock : Option Clock) (index : Nat) (connection : Connection) :
      Branch (.pure value) clock index connection { outputs := [], connection, value := some value }
  /-- A stopping step records its reason and does not execute the continuation. -/
  | stopped {statement values rest clock index connection reason}
      (step : runScriptStep runContext clock index connection statement values = .ended reason) :
      Branch (.exec statement values rest) clock index connection
        { outputs := [.unmodeled reason], connection, value := none }
  /-- A continued step passes the selected output of the chosen execution and the exact next
  connection of that execution to the next program, at the next index with the same clock, and
  prefixes that output to its trace. -/
  | continued {statement values rest clock index connection actual next others found selected result}
      (step : runScriptStep runContext clock index connection statement values = .continued actual next others)
      (member : found ∈ (RunStep.continued actual next others).executions)
      (choice : OutputChoice found.output selected)
      (later : Branch (rest selected) clock (index + 1) found.next result) :
      Branch (.exec statement values rest) clock index connection
        { result with outputs := selected :: result.outputs }

/-- A continued step with the model's own execution: the branch that passes the selected output
of the step's own output and its next connection. It is {name}`Sql.Branch.continued` with the first
execution of the step. Proof sketch: the own execution is the head of the executions. -/
theorem Sql.Branch.continued_own {α : Type} {statement values rest clock index connection actual next others selected}
    {result : SqlRun α}
    (step : runScriptStep runContext clock index connection statement values = .continued actual next others)
    (choice : OutputChoice actual selected)
    (later : Branch (rest selected) clock (index + 1) next result) :
    Branch (.exec statement values rest) clock index connection
      { result with outputs := selected :: result.outputs } :=
  .continued (found := { output := actual, next }) step (by simp [RunStep.executions]) choice later

/-- For any actual output, choosing that raw output is permitted, including an empty
alternative wrapper. Proof sketch: the first disjunct of {name}`OutputChoice`. -/
theorem OutputChoice.actual (output : Output) : OutputChoice output output := Or.inl rfl

/-- For every listed rows result, choosing its concrete output is permitted. There is no
obligation on rows outside the list. Proof sketch: the second disjunct supplies membership. -/
theorem OutputChoice.rows {alternatives : List (List (List Value))} {rows : List (List Value)}
    (member : rows ∈ alternatives) : OutputChoice (.oneOf alternatives) (.rows rows) :=
  Or.inr ⟨rows, member, rfl⟩

end Belay.Sqlite
