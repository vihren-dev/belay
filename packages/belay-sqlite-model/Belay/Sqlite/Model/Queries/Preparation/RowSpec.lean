import Belay.Sqlite.Model.Queries.Preparation.ColumnSpec
import Belay.Sqlite.Model.Queries.Evaluation.InsertCells

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For a successful {name}`resolveAllFrom`, the result has one value per item, and
for each index with an item, the value at that index is the result of resolving the
item at the start position plus the index. Proof sketch: induction on the items;
the head's value comes first and every later index moves by one. -/
theorem resolveAllFrom_ok (resolveOne : Nat → α → Except ε β) (start : Nat)
    (items : List α) (values : List β) (ok : resolveAllFrom resolveOne start items = .ok values) :
    values.length = items.length ∧ ∀ index item, items[index]? = some item →
      ∃ value, values[index]? = some value ∧ resolveOne (start + index) item = .ok value := by
  induction items generalizing start values with
  | nil => cases ok; simp
  | cons item rest ih =>
    simp only [resolveAllFrom, bind, Except.bind] at ok
    split at ok <;> try contradiction
    rename_i value head
    split at ok <;> try contradiction
    rename_i tail_values tail
    cases ok
    obtain ⟨length, each⟩ := ih (start + 1) tail_values tail
    refine ⟨by simp [length], fun index found h => ?_⟩
    cases index with
    | zero => simp at h; subst h; exact ⟨value, rfl, by simpa using head⟩
    | succ index =>
      obtain ⟨v, hv, hr⟩ := each index found (by simpa using h)
      exact ⟨v, by simpa using hv, by simpa [Nat.add_assoc, Nat.add_comm 1 index] using hr⟩

end Belay.Sqlite.Model
