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
returns no value. A continued step chooses an allowed observation, passes it to the
continuation, and records it in the trace. SQL errors continue in the same way as other
modeled outputs. Every step uses {name}`runScriptStep`; this relation adds no evaluator. -/
inductive Sql.Branch {α : Type} : Sql α → Option Clock → Nat → Connection → SqlRun α → Prop where
  /-- Pure returns its value without changing the connection or producing an output. -/
  | pure (value : α) (clock : Option Clock) (index : Nat) (connection : Connection) :
      Branch (.pure value) clock index connection { outputs := [], connection, value := some value }
  /-- A stopping step records its reason and does not execute the continuation. -/
  | stopped {statement values rest clock index connection reason}
      (step : runScriptStep runContext clock index connection statement values = .ended reason) :
      Branch (.exec statement values rest) clock index connection
        { outputs := [.unmodeled reason], connection, value := none }
  /-- A continued step passes the selected output and exact next connection to the next
  program, at the next index with the same clock, and prefixes that output to its trace. -/
  | continued {statement values rest clock index connection actual next selected result}
      (step : runScriptStep runContext clock index connection statement values = .continued actual next)
      (choice : OutputChoice actual selected)
      (later : Branch (rest selected) clock (index + 1) next result) :
      Branch (.exec statement values rest) clock index connection
        { result with outputs := selected :: result.outputs }

/-- For any actual output, choosing that raw output is permitted, including an empty
alternative wrapper. Proof sketch: the first disjunct of {name}`OutputChoice`. -/
theorem OutputChoice.actual (output : Output) : OutputChoice output output := Or.inl rfl

/-- For every listed rows result, choosing its concrete output is permitted. There is no
obligation on rows outside the list. Proof sketch: the second disjunct supplies membership. -/
theorem OutputChoice.rows {alternatives : List (List (List Value))} {rows : List (List Value)}
    (member : rows ∈ alternatives) : OutputChoice (.oneOf alternatives) (.rows rows) :=
  Or.inr ⟨rows, member, rfl⟩

end Belay.Sqlite
