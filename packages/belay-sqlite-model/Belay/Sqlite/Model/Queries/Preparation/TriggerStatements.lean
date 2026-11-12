import Belay.Sqlite.Model.Queries.Select.TriggerBodies

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The outcome of a traced computation changed as a whole, with the trace kept. -/
def Traced.mapResult {ε ε' α β : Type} (change : Except ε α → Except ε' β) (computation : Traced ε α) :
    Traced ε' β :=
  ⟨change computation.drop, computation.trace⟩

/-- The occurrence moved from the column that resolves a message to the place of the message in the written
column: {lit}`paths` are the places of the messages ({name}`raiseMessagePaths`). -/
def moveToMessage (paths : List (List Nat)) (occurrence : NameOccurrence) : NameOccurrence :=
  match occurrence.path with
  | 0 :: (column + 1) :: 0 :: rest => match paths[column]? with
    | some place => { occurrence with path := [0, 0, 0] ++ place ++ rest }
    | none => occurrence
  | _ => occurrence

end Belay.Sqlite.Model
