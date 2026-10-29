import Std

set_option doc.verso true

namespace ProofBoundaries

/-- The actual observation and the predicate of possible observations of one execution.
For example, an identity observer retains complete results; another observer can retain
only a value and trace. Equality of these profiles uses ordinary equality laws. -/
def observationProfile {Result Observation : Type} (actual : Result)
    (branches : Result → Prop) (observe : Result → Observation) : Observation × (Observation → Prop) :=
  (observe actual, fun observed => ∃ result, branches result ∧ observe result = observed)

/-- Two observation profiles are equal exactly when their actual observations and every
possible-observation proposition agree. Proof sketch: extensionality for the predicate field. -/
theorem observationProfile_eq_iff {Left Right Observation : Type}
    (actualLeft : Left) (actualRight : Right) (left : Left → Prop) (right : Right → Prop)
    (observeLeft : Left → Observation) (observeRight : Right → Observation) :
    observationProfile actualLeft left observeLeft = observationProfile actualRight right observeRight ↔
      observeLeft actualLeft = observeRight actualRight ∧ ∀ observed,
        (∃ result, left result ∧ observeLeft result = observed) ↔
        (∃ result, right result ∧ observeRight result = observed) := by
  constructor
  · intro same
    exact ⟨congrArg Prod.fst same, fun observed =>
      Iff.of_eq (congrArg (fun profile => profile.2 observed) same)⟩
  · rintro ⟨actual, possible⟩
    exact Prod.ext actual (funext fun observed => propext (possible observed))

/-- If old observations match, actual results are permitted branches, and every pair
of branches with equal old observations also has equal new observations, then the new
profiles match. Proof sketch: reuse each old branch match and its supplied implication. -/
theorem observationProfile_transport {Left Right Old New : Type}
    {actualLeft : Left} {actualRight : Right} {left : Left → Prop} {right : Right → Prop}
    {oldLeft : Left → Old} {oldRight : Right → Old} {newLeft : Left → New} {newRight : Right → New}
    (same : observationProfile actualLeft left oldLeft = observationProfile actualRight right oldRight)
    (actualL : left actualLeft) (actualR : right actualRight)
    (transport : ∀ one two, left one → right two → oldLeft one = oldRight two → newLeft one = newRight two) :
    observationProfile actualLeft left newLeft = observationProfile actualRight right newRight := by
  obtain ⟨actual, possible⟩ := (observationProfile_eq_iff _ _ _ _ _ _).mp same
  apply (observationProfile_eq_iff _ _ _ _ _ _).mpr
  refine ⟨transport _ _ actualL actualR actual, fun observed => ?_⟩
  constructor
  · rintro ⟨one, branch, seen⟩
    obtain ⟨two, matched, equal⟩ := (possible (oldLeft one)).mp ⟨one, branch, rfl⟩
    exact ⟨two, matched, (transport one two branch matched equal.symm).symm.trans seen⟩
  · rintro ⟨two, branch, seen⟩
    obtain ⟨one, matched, equal⟩ := (possible (oldRight two)).mpr ⟨two, branch, rfl⟩
    exact ⟨one, matched, (transport one two matched branch equal).trans seen⟩

/-- A branch predicate that holds exactly at the actual result has the singleton
observation profile. Proof sketch: replace each branch by that result. -/
theorem observationProfile_singleton {Result Observation : Type}
    (actual : Result) (branches : Result → Prop) (observe : Result → Observation)
    (only : ∀ result, branches result ↔ result = actual) :
    observationProfile actual branches observe = (observe actual, fun observed => observe actual = observed) := by
  apply Prod.ext
  · rfl
  · funext observed
    simp only [observationProfile, only, exists_eq_left]

/-- Two executions with one possible result have equal observation profiles whenever
their actual observations agree. Proof sketch: both profiles are singleton profiles. -/
theorem observationProfile_of_singletons {Left Right Observation : Type}
    (actualLeft : Left) (actualRight : Right) (left : Left → Prop) (right : Right → Prop)
    (observeLeft : Left → Observation) (observeRight : Right → Observation)
    (onlyLeft : ∀ result, left result ↔ result = actualLeft)
    (onlyRight : ∀ result, right result ↔ result = actualRight)
    (same : observeLeft actualLeft = observeRight actualRight) :
    observationProfile actualLeft left observeLeft = observationProfile actualRight right observeRight := by
  rw [observationProfile_singleton _ _ _ onlyLeft, observationProfile_singleton _ _ _ onlyRight, same]

#print axioms observationProfile_eq_iff
#print axioms observationProfile_transport
#print axioms observationProfile_singleton
#print axioms observationProfile_of_singletons
end ProofBoundaries
