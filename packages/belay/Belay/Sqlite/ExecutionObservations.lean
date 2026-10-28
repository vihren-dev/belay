import Belay.Sqlite.ExecutionEquivalenceLaws

set_option doc.verso true

namespace Belay.Sqlite

/-- The optional return value and complete output trace of a run, omitting its connection.
For example, equal observations can hide different pragma settings or counters. Use the
complete {name}`Sql.EquivAt` relation when continuations may inspect connection state. -/
def SqlRun.observation {α : Type} (result : SqlRun α) : Option α × List Output :=
  (result.value, result.outputs)

/-- At one shared context, the actual runs have the same return value and outputs, and the
sets of branch return values and outputs agree. All final connections are omitted. This
comparison has no unrestricted bind or append congruence: later SQL can read omitted state.
The full trace, including errors and unmodeled reasons, is still observed. -/
def Sql.ObservationEquivAt {α : Type} (first second : Sql α)
    (state : ExecutionContext) : Prop :=
  observationProfile (first.runFrom state.clock state.index state.connection)
    (first.Branch state.clock state.index state.connection) SqlRun.observation =
  observationProfile (second.runFrom state.clock state.index state.connection)
    (second.Branch state.clock state.index state.connection) SqlRun.observation

/-- Complete fixed-context equivalence implies equality of return values and output traces
for the actual run and the sets of branches. Proof sketch: project actual equality and
reuse each identical branch outcome before discarding its final connection. -/
theorem Sql.EquivAt.observation {α : Type} {first second : Sql α} {state : ExecutionContext}
    (same : first.EquivAt second state) : first.ObservationEquivAt second state := by
  exact observationProfile_transport same (Sql.Branch.actual first _ _ _)
    (Sql.Branch.actual second _ _ _) (fun _ _ _ _ equal => congrArg SqlRun.observation equal)

end Belay.Sqlite
