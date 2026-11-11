import Belay.Sqlite.Programs.Claims.CheckClaim

set_option doc.verso true

namespace Belay.Sqlite

/-- What a report shows of a run: whether the program returned a value, and the outputs of its statements. -/
def Sql.runSummary {α : Type} (program : Sql α) (state : ExecutionContext) : Bool × List Output :=
  let run := program.runFrom state.clock state.index state.connection
  (run.value.isSome, run.outputs)

/-- The check of a program at one run: the actual run of the program from the context must return a value that
satisfies the postcondition at the context that the run reaches. This is the check of {name}`Sql.check`
restricted to the actual branch, so a failure here is a failure of that check. -/
def Sql.checkActual {α : Type} (program : Sql α) (post : α → ExecutionContext → Prop)
    (state : ExecutionContext) : Prop :=
  match (program.runFrom state.clock state.index state.connection).value with
  | none => False
  | some value => post value (state.finish (program.runFrom state.clock state.index state.connection))

/-- The check of the actual run is decidable when the postcondition is. -/
instance Sql.decidableCheckActual {α : Type} (program : Sql α) (post : α → ExecutionContext → Prop)
    [∀ value state, Decidable (post value state)] (state : ExecutionContext) :
    Decidable (program.checkActual post state) := by
  unfold Sql.checkActual
  split <;> infer_instance

end Belay.Sqlite
