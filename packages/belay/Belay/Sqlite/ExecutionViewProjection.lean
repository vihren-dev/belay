import Belay.Sqlite.ExecutionView

set_option doc.verso true

namespace Belay.Sqlite

/-- Project a recorded trace through the annotation of its exact program. Continued steps
select their view using the recorded raw or concrete output. A stopping output ends this
walk. Any unmatched trace suffix is retained. This function reads outputs; it executes no SQL.
Use the trace from the program's ordinary run or a permitted branch. -/
def Sql.View.project {α : Type} {program : Sql α} (view : View program)
    (outputs : List Output) : List Output :=
  match view, outputs with
  | .pure _, outputs => outputs
  | .exec _ _, [] => []
  | .exec hideSuccessful later, output :: rest =>
    if output.endsRun then output :: rest
    else
      let projected := (later output).project rest
      if hideSuccessful && !output.isError then projected else output :: projected

/-- The original optional return value with the projected trace. A returned value can itself
contain migration outputs; projection leaves that value unchanged. Final connection state
is omitted, so this observation alone does not justify replacing later SQL computations. -/
def Sql.View.observation {α : Type} {program : Sql α} (view : View program)
    (result : SqlRun α) : Option α × List Output :=
  (result.value, view.project result.outputs)

/-- Finish the original run, then replace only its newly observed trace with the projection.
The starting trace is retained. In particular, the next index counts every raw step,
including hidden outputs and a stopping step; later SQL keeps its actual clock assignment. -/
def Sql.View.finish {α : Type} {program : Sql α} (view : View program)
    (state : ExecutionContext) (result : SqlRun α) : ExecutionContext :=
  { state.finish result with outputs := state.outputs ++ view.project result.outputs }

/-- The original optional return value and the full reached context with a projected trace.
All connection fields, the clock and the raw next-statement index remain observable.
Use this observation when a comparison must retain effects that later SQL can inspect. -/
def Sql.View.fullObservation {α : Type} {program : Sql α} (view : View program)
    (state : ExecutionContext) (result : SqlRun α) : Option α × ExecutionContext :=
  (result.value, view.finish state result)

end Belay.Sqlite
