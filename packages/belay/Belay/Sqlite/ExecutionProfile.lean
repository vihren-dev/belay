import Std

set_option doc.verso true

/-! Actual and permitted observations share one representation for execution comparisons. -/

namespace Belay.Sqlite

/-- An actual observation and the predicate of permitted observations. For example,
use the identity observer to retain complete results, or a projection to compare
only visible fields. The actual observation remains separate from the predicate. -/
def observationProfile {Result Observation : Type} (actual : Result)
    (branches : Result → Prop) (observe : Result → Observation) :
    Observation × (Observation → Prop) :=
  (observe actual, fun observed => ∃ result, branches result ∧ observe result = observed)

/-- Equal profiles have equal actual observations. Proof sketch: project the first
component of the pair; equality of the permitted observations alone is insufficient. -/
theorem observationProfile_actual {Left Right Observation : Type}
    {actualLeft : Left} {actualRight : Right} {left : Left → Prop} {right : Right → Prop}
    {observeLeft : Left → Observation} {observeRight : Right → Observation}
    (same : observationProfile actualLeft left observeLeft = observationProfile actualRight right observeRight) :
    observeLeft actualLeft = observeRight actualRight := congrArg Prod.fst same

/-- Two profiles are equal exactly when their actual observations agree and each
observation is permitted on one side exactly when it is permitted on the other.
Proof sketch: pair equality and function extensionality separate the two components. -/
theorem observationProfile_eq_iff {Left Right Observation : Type}
    {actualLeft : Left} {actualRight : Right} {left : Left → Prop} {right : Right → Prop}
    {observeLeft : Left → Observation} {observeRight : Right → Observation} :
    observationProfile actualLeft left observeLeft = observationProfile actualRight right observeRight ↔
      observeLeft actualLeft = observeRight actualRight ∧ ∀ observed,
        (∃ result, left result ∧ observeLeft result = observed) ↔
        (∃ result, right result ∧ observeRight result = observed) := by
  constructor
  · intro same
    exact ⟨observationProfile_actual same, fun observed =>
      Iff.of_eq (congrArg (fun profile => profile.2 observed) same)⟩
  · rintro ⟨actual, possible⟩
    exact Prod.ext actual (funext fun observed => propext (possible observed))

/-- Identity profiles agree exactly when the actual results agree and both sides
permit the same results. Proof sketch: each identity observation identifies its result. -/
theorem observationProfile_id_eq_iff {Result : Type}
    {actualLeft actualRight : Result} {left right : Result → Prop} :
    observationProfile actualLeft left id = observationProfile actualRight right id ↔
      actualLeft = actualRight ∧ ∀ result, left result ↔ right result := by
  simp only [observationProfile_eq_iff, id_eq, exists_eq_right]

/-- Equal profiles remain equal under new observers if matching permitted results
have equal new observations. Both actual results must be permitted. No claim is
required for pairs whose old observations differ. Proof sketch: reuse each old
branch match and apply the observer implication, including to the actual results. -/
theorem observationProfile_transport {Left Right Old New : Type}
    {actualLeft : Left} {actualRight : Right} {left : Left → Prop} {right : Right → Prop}
    {oldLeft : Left → Old} {oldRight : Right → Old} {newLeft : Left → New} {newRight : Right → New}
    (same : observationProfile actualLeft left oldLeft = observationProfile actualRight right oldRight)
    (actualL : left actualLeft) (actualR : right actualRight)
    (transport : ∀ one two, left one → right two → oldLeft one = oldRight two → newLeft one = newRight two) :
    observationProfile actualLeft left newLeft = observationProfile actualRight right newRight := by
  obtain ⟨actual, possible⟩ := observationProfile_eq_iff.mp same
  apply observationProfile_eq_iff.mpr
  refine ⟨transport _ _ actualL actualR actual, fun observed => ?_⟩
  constructor
  · rintro ⟨one, branch, seen⟩
    obtain ⟨two, matched, equal⟩ := (possible (oldLeft one)).mp ⟨one, branch, rfl⟩
    exact ⟨two, matched, (transport one two branch matched equal.symm).symm.trans seen⟩
  · rintro ⟨two, branch, seen⟩
    obtain ⟨one, matched, equal⟩ := (possible (oldRight two)).mpr ⟨two, branch, rfl⟩
    exact ⟨one, matched, (transport one two matched branch equal).trans seen⟩

/-- If each side permits exactly its actual result, equal actual observations give
equal profiles. Proof sketch: substitute each permitted result with its actual
result, so both predicates describe the same single observation. -/
theorem observationProfile_of_singletons {Left Right Observation : Type}
    {actualLeft : Left} {actualRight : Right} {left : Left → Prop} {right : Right → Prop}
    {observeLeft : Left → Observation} {observeRight : Right → Observation}
    (onlyLeft : ∀ result, left result ↔ result = actualLeft)
    (onlyRight : ∀ result, right result ↔ result = actualRight)
    (same : observeLeft actualLeft = observeRight actualRight) :
    observationProfile actualLeft left observeLeft = observationProfile actualRight right observeRight := by
  apply observationProfile_eq_iff.mpr
  simp only [onlyLeft, onlyRight, exists_eq_left, same, iff_self, implies_true, and_self]

end Belay.Sqlite
