import Belay.Sqlite.Model.Values.Scalar.ReadDefaults
import Belay.Sqlite.Model.Values.Scalar.StoreValueLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every affinity, token and negation flag, storing the result of
{name}`readNumericDefault` again leaves it unchanged. The proof uses the
idempotence of {name}`Value.store`; no valid-token assumption is needed. -/
theorem readNumericDefault_stored (affinity : Affinity) (token : String) (negated : Bool) :
    Value.store affinity (readNumericDefault affinity token negated) = readNumericDefault affinity token negated := by
  unfold readNumericDefault
  exact Value.store_store _ _

end Belay.Sqlite.Model
