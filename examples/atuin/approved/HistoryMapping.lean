import SchemaBinding
import HistoryDecoding

/-! The approved mapping reads the complete pre-migration business model from
storage. Undefined decoding rejects the complete observation. -/
namespace HistoryMapping
open Belay.Sqlite SqliteVerifier HistoryModel

/-- Every physical history row contributes one decoded business entry. The history
table is at its position in the sealed starting catalog; positions do not change. -/
def observe (database : Database) : Option (List History) := do
  let position ← tablePosition SchemaBinding.start "history"
  let table ← database position
  HistoryDecoding.decodeRows (table.project SchemaBinding.fields)

/-- Catalog conformance under the profile and complete decoding establish the
represented business state. -/
def representation (profile : Profile) (catalog : Catalog) (database : Database) : Prop :=
  Conforms profile catalog database ∧ ∃ histories, observe database = some histories

/-- Every canonical observation lies in the independent business model's domain. -/
theorem observe_valid (observed : observe database = some histories) :
    ∀ history ∈ histories, history.Valid := by
  unfold observe at observed
  simp only [bind, Option.bind_eq_some_iff] at observed
  obtain ⟨_, _, table, _, decoded⟩ := observed
  exact HistoryDecoding.decodeRows_valid decoded

end HistoryMapping
