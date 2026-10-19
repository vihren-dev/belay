import Belay.Sqlite.Resolution.ReadDefaults
import Belay.Sqlite.StoreValueLaws

set_option doc.verso true

/-! Laws of the defaults that old rows read after ADD COLUMN ({lit}`ReadDefaults.lean`): the
value that {lit}`readDefaultValue` gives is already stored with the column's affinity. They
are kept apart from the definitions, as {lit}`StoreValueLaws.lean` is from
{lit}`StoreValue.lean`, so that execution does not import the laws of {lit}`storeValue`. -/

namespace Belay.Sqlite

/-- For every affinity, token and negation flag, storing the result of
{name}`readNumericDefault` again leaves it unchanged. The proof uses the
idempotence of {name}`storeValue`; no valid-token assumption is needed. -/
theorem readNumericDefault_stored (affinity : Affinity) (token : String) (negated : Bool) :
    storeValue affinity (readNumericDefault affinity token negated) = readNumericDefault affinity token negated := by
  unfold readNumericDefault
  exact storeValue_storeValue _ _

/-- For every column and value, if {name}`readDefaultValue` returns that value,
storing it with the column's affinity leaves it unchanged. An error return
satisfies no premise. The proof splits the stored default forms: no default reads NULL,
and a literal default reads its value stored with the affinity
({name}`storeValue_storeValue`). -/
theorem readDefaultValue_stored (column : CatalogColumn) (value : Value)
    (accepted : readDefaultValue column = .ok value) : storeValue column.affinity value = value := by
  unfold readDefaultValue at accepted
  split at accepted
  · cases accepted; exact storeValue_null _
  · cases accepted; exact storeValue_storeValue _ _
  · cases accepted

end Belay.Sqlite
