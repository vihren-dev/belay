import Belay.Sqlite.Model.Queries.Evaluation.QueryResults
import Belay.Sqlite.Model.Queries.Evaluation.ExceptCombineLaws

set_option doc.verso true

/-! The rules of the {lit}`distinct` phase of a query (ADR 0027, D1): {lit}`SELECT DISTINCT` keeps
the first record of each set of records whose rows compare equal under the collations of the result
columns ({name}`Belay.Sqlite.Model.Resolved.sameOutput`). The kept records are a sublist of the
records, so a property of every record holds of every kept one; no two kept rows compare equal; and
each record has a kept record whose row compares equal to its row. Equal rows need not be the same
values: {lit}`1` and {lit}`1.0`, or {lit}`'a'` and {lit}`'A'` under {lit}`NOCASE`, compare equal,
and the kept value is the first one. The laws hold for every fold that keeps the first item of each
set of equal items, which {lit}`distinctRows` of a compound also is. -/

namespace Belay.Sqlite.Model.Resolved

/-- One step of keeping the first item of equal items: an item whose key is the same as the key of
a kept item ({lit}`same`) is dropped, else it is kept at the end. -/
def keepFirst {α β : Type} (same : β → β → Bool) (key : α → β) (kept : List α) (item : α) : List α :=
  if kept.any fun earlier => same (key earlier) (key item) then kept else kept ++ [item]

/-- Keep-first rule: for every test, key, items and kept items, the fold of {name}`keepFirst`
from the kept items:
- is a sublist of the kept items followed by the items;
- keeps every kept item;
- has, for each item, a kept item that is the item or whose key is the same as its key;
- has no two items, an earlier and a later one, whose keys are the same with the later key second,
  when the kept items had none.

Proof sketch: induction on the items; a dropped item has a kept item with the same key, and a kept
item has no earlier item with the same key. -/
theorem keepFirst_fold {α β : Type} (same : β → β → Bool) (key : α → β) :
    ∀ (items kept : List α),
      (items.foldl (keepFirst same key) kept).Sublist (kept ++ items) ∧
        (∀ item ∈ kept, item ∈ items.foldl (keepFirst same key) kept) ∧
        (∀ item ∈ items, ∃ chosen ∈ items.foldl (keepFirst same key) kept,
          chosen = item ∨ same (key chosen) (key item) = true) ∧
        (kept.Pairwise (fun earlier later => same (key earlier) (key later) = false) →
          (items.foldl (keepFirst same key) kept).Pairwise (fun earlier later => same (key earlier) (key later) = false))
  | [], kept => ⟨by simp, fun _ member => member, by simp, id⟩
  | item :: rest, kept => by
    obtain ⟨sublist, keeps, covers, pairwise⟩ := keepFirst_fold same key rest (keepFirst same key kept item)
    simp only [List.foldl_cons]
    by_cases found : (kept.any fun earlier => same (key earlier) (key item)) = true
    · have step : keepFirst same key kept item = kept := by simp [keepFirst, found]
      rw [step] at sublist keeps covers pairwise ⊢
      obtain ⟨earlier, member, sameKey⟩ := List.any_eq_true.mp found
      refine ⟨sublist.trans (by simp), keeps,
        fun other inItems => ?_, pairwise⟩
      rcases List.mem_cons.mp inItems with rfl | later
      · exact ⟨earlier, keeps earlier member, .inr sameKey⟩
      · exact covers other later
    · have step : keepFirst same key kept item = kept ++ [item] := by simp [keepFirst, found]
      rw [step] at sublist keeps covers pairwise ⊢
      refine ⟨by simpa using sublist, fun other member => keeps other (List.mem_append_left _ member),
        fun other inItems => ?_, fun before => pairwise ?_⟩
      · rcases List.mem_cons.mp inItems with rfl | later
        · exact ⟨other, keeps other (by simp), .inl rfl⟩
        · exact covers other later
      · rw [List.pairwise_append]
        refine ⟨before, by simp, fun earlier member later single => ?_⟩
        rw [List.mem_singleton.mp single]
        simpa using List.any_eq_false.mp (by simpa using found) earlier member

/-- For every collations and two rows, {name}`sameOutput` is symmetric: the rows compare equal in
one order exactly when they compare equal in the other. Proof sketch: the lengths agree in both
orders, and a collation's comparison is equal in one order exactly when it is in the other. -/
theorem sameOutput_comm (collations : List Collation) (first second : List Value) :
    sameOutput collations first second = sameOutput collations second first := by
  unfold sameOutput
  have lengths : (first.length == second.length) = (second.length == first.length) :=
    Bool.eq_iff_iff.mpr ⟨fun equal => beq_iff_eq.mpr (beq_iff_eq.mp equal).symm,
      fun equal => beq_iff_eq.mpr (beq_iff_eq.mp equal).symm⟩
  rw [lengths]
  congr 1
  clear lengths
  induction collations generalizing first second with
  | nil => simp
  | cons collation rest ih =>
    cases first with
    | nil => cases second <;> simp
    | cons a as =>
      cases second with
      | nil => simp
      | cons b bs =>
        simp only [List.zip_cons_cons, List.all_cons]
        rw [ih as bs, Std.OrientedCmp.eq_swap (cmp := collation.compare) (a := a) (b := b)]
        cases collation.compare b a <;> rfl

/-- Distinct rule: for every collations and records, the records of {lit}`SELECT DISTINCT`
({name}`distinctRecords`):
- are a sublist of the records;
- have, for each record, a kept record that is the record or whose row compares equal to its row
  ({name}`sameOutput`);
- have no two records whose rows compare equal.

Proof sketch: {name}`distinctRecords` is the fold of {name}`keepFirst` with the rows as keys, and
{name}`keepFirst_fold` from no kept record. -/
theorem distinctRecords_rules (collations : List Collation) (found : List Record) :
    (distinctRecords collations found).Sublist found ∧
      (∀ record ∈ found, ∃ kept ∈ distinctRecords collations found,
        kept = record ∨ sameOutput collations kept.1 record.1 = true) ∧
      (distinctRecords collations found).Pairwise (fun earlier later => sameOutput collations earlier.1 later.1 = false) := by
  have fold : distinctRecords collations found = found.foldl (keepFirst (sameOutput collations) Prod.fst) [] := rfl
  obtain ⟨sublist, -, covers, pairwise⟩ := keepFirst_fold (sameOutput collations) Prod.fst found []
  rw [fold]
  exact ⟨by simpa using sublist, covers, pairwise .nil⟩

/-- For every context, query that is no compound and has {lit}`DISTINCT` with collations, and rows,
the records of the query ({name}`Query.uniqueRecords`) are the distinct records
({name}`distinctRecords`) of the records ({name}`records`) of the rows that {lit}`WHERE` keeps
({name}`filtered`). Proof sketch: {name}`Query.uniqueRecords` takes its branch of a query that is
no compound and has {lit}`DISTINCT`. -/
theorem Query.uniqueRecords_distinct (context : EvalContext) {query : Query} {collations : List Collation}
    (single : query.compound = none) (distinct : query.distinct = some collations) (rows : List (List Value)) :
    query.uniqueRecords context rows = distinctRecords collations (records context query (filtered context query rows)) := by
  simp [Query.uniqueRecords, single, distinct]

/-- Unique-rows rule: for every collations and rows, when no two rows compare equal
({name}`sameOutput`) in list order, no two rows of any permutation of them compare equal. Proof
sketch: {name}`sameOutput` is symmetric ({name}`sameOutput_comm`), and a permutation keeps a
symmetric pairwise property. -/
theorem pairwise_sameOutput_perm (collations : List Collation) {rows other : List (List Value)}
    (unique : rows.Pairwise fun earlier later => sameOutput collations earlier later = false) (perm : other.Perm rows) :
    other.Pairwise fun earlier later => sameOutput collations earlier later = false :=
  perm.symm.pairwise unique fun different => by rw [sameOutput_comm]; exact different

end Belay.Sqlite.Model.Resolved
