import Belay.Sqlite.Model.Queries.Preparation.TriggerStatements

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- A computation that may fail, run so that its failure is a value: the outcome is the
computation's {lit}`Except` and the trace stays, also after a failure. -/
def Traced.attempt {ε ε' α : Type} (computation : Traced ε α) : Traced ε' (Except ε α) :=
  ⟨.ok computation.drop, computation.trace⟩

end Belay.Sqlite.Model
