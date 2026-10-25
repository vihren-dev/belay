import Belay.Sqlite.ExecutionViewProjection

set_option doc.verso true

namespace Belay.Sqlite

/-- For every program and recorded trace, the identity view retains the complete trace.
Proof sketch: induction on the program follows each recorded continuation output. -/
theorem Sql.View.project_identity {α : Type} (program : Sql α) (outputs : List Output) :
    (identity program).project outputs = outputs := by
  induction program generalizing outputs with
  | pure => rfl
  | exec statement values rest later =>
    cases outputs with
    | nil => rfl
    | cons output outputs =>
      simp only [identity, uniform, project]
      split
      · rfl
      · simpa only [identity, Bool.false_and, Bool.false_eq_true, ↓reduceIte] using
          congrArg (output :: ·) (later output outputs)

/-- For every view and trace, projecting retains exactly the same errors and stopping
outputs, in the same order. No execution assumption is needed. Proof sketch: each deleted
output is a successful continued output; induction preserves the remaining suffix. -/
theorem Sql.View.project_failures {α : Type} {program : Sql α} (view : View program)
    (outputs : List Output) :
    (view.project outputs).filter (fun output => output.isError || output.endsRun) =
      outputs.filter (fun output => output.isError || output.endsRun) := by
  induction view generalizing outputs with
  | pure => rfl
  | exec hideSuccessful later hypothesis =>
    cases outputs with
    | nil => rfl
    | cons output outputs =>
      simp only [project]
      split
      · rfl
      · rename_i continued
        split
        · rename_i hidden
          have successful : output.isError = false := by
            cases failure : output.isError <;> simp_all
          simp [continued, successful, hypothesis output outputs]
        · simp only [List.filter_cons]
          rw [hypothesis output outputs]

/-- For every view and result, weak projection retains its optional return value exactly,
including any outputs stored in that value. Proof sketch: the first projection is unchanged. -/
theorem Sql.View.observation_value {α : Type} {program : Sql α} (view : View program)
    (result : SqlRun α) : (view.observation result).1 = result.value := rfl

/-- For every view and result, the full observation retains the original return value.
Proof sketch: the first projection is unchanged. -/
theorem Sql.View.fullObservation_value {α : Type} {program : Sql α} (view : View program)
    (state : ExecutionContext) (result : SqlRun α) :
    (view.fullObservation state result).1 = result.value := rfl

/-- For every view and run, the reached index advances by the complete raw trace length,
regardless of how many outputs are hidden. Proof sketch: finish changes only the trace. -/
theorem Sql.View.finish_index {α : Type} {program : Sql α} (view : View program)
    (state : ExecutionContext) (result : SqlRun α) :
    (view.finish state result).index = state.index + result.outputs.length := rfl

/-- For every view and run, projection retains the original statement-indexed clock.
Proof sketch: finish changes only the trace. -/
theorem Sql.View.finish_clock {α : Type} {program : Sql α} (view : View program)
    (state : ExecutionContext) (result : SqlRun α) :
    (view.finish state result).clock = state.clock := rfl

/-- For every view and run, projection retains the run's complete final connection,
including counters and transaction snapshots. Proof sketch: finish changes only the trace. -/
theorem Sql.View.finish_connection {α : Type} {program : Sql α} (view : View program)
    (state : ExecutionContext) (result : SqlRun α) :
    (view.finish state result).connection = result.connection := rfl

/-- For every view and run, the starting trace precedes the projected new trace unchanged.
Proof sketch: this is the trace field in the definition of finish. -/
theorem Sql.View.finish_outputs {α : Type} {program : Sql α} (view : View program)
    (state : ExecutionContext) (result : SqlRun α) :
    (view.finish state result).outputs = state.outputs ++ view.project result.outputs := rfl

/-- For every program, context and run, the identity view gives the ordinary full reached
context. Proof sketch: the identity trace law reduces the sole replaced field. -/
theorem Sql.View.finish_identity {α : Type} (program : Sql α) (state : ExecutionContext)
    (result : SqlRun α) : (identity program).finish state result = state.finish result := by
  simp [finish, project_identity, ExecutionContext.finish]

end Belay.Sqlite
